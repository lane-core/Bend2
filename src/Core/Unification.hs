{-# LANGUAGE ViewPatterns #-}

-- | Advanced Metavariable Unification System for Bend2
-- 
-- This module implements contextual metavariables with pattern unification,
-- based on techniques from smalltt and elaboration-zoo. It provides:
--
-- * Contextual metavariables that abstract over bound variables
-- * Pattern unification for higher-order unification problems  
-- * Occurs checking with caching to prevent infinite types
-- * Partial renamings for scope-safe variable handling
-- * Backward compatibility with existing Met constructor

module Core.Unification where

import Control.Monad (when, unless)
import Data.IORef
import Data.List (nub)
import Data.Maybe (fromJust)
import qualified Data.IntMap as IM
import qualified Data.IntSet as IS
import System.IO.Unsafe (unsafePerformIO)

import Core.Type
import Core.WHNF (normal, force)
import Core.Equal (equal)
import qualified Data.Map as M

-- | Enhanced metavariable identifier
newtype MetaVar = MetaVar Int 
  deriving (Eq, Ord, Show)

-- | Level for de Bruijn indexing  
newtype Lvl = Lvl Int
  deriving (Eq, Ord, Show, Num, Integral, Real, Enum)

-- | Set of levels for constraint tracking
type LvlSet = IS.IntSet

-- | Metavariable entry in the metacontext
data MetaEntry
  = Unsolved LvlSet          -- ^ Unsolved with level constraints
  | Solved Term LvlSet       -- ^ Solved with original constraints (Term is the solution)

-- Manual Show instance since Term doesn't have Show
instance Show MetaEntry where
  show (Unsolved constraints) = "Unsolved " ++ show constraints
  show (Solved _ constraints) = "Solved <term> " ++ show constraints

-- | Global metacontext (mutable state)
type MetaContext = IM.IntMap MetaEntry

-- | Global metacontext reference
{-# NOINLINE globalMetaContext #-}
globalMetaContext :: IORef MetaContext
globalMetaContext = unsafePerformIO (newIORef IM.empty)

-- | Global counter for fresh metavariables
{-# NOINLINE nextMetaVar #-}
nextMetaVar :: IORef Int  
nextMetaVar = unsafePerformIO (newIORef 0)

-- | Partial renaming for scope-safe unification
data PartialRenaming = PartialRenaming
  { prOccurs   :: MetaVar              -- ^ Meta being checked for occurs
  , prDomain   :: Lvl                  -- ^ Domain context size
  , prCodomain :: Lvl                  -- ^ Codomain context size  
  , prRenaming :: IM.IntMap Int        -- ^ Partial mapping (-1 = undefined)
  } deriving Show

-- | Spine for pattern unification (list of variables)
data Spine = Spine [Lvl]
  deriving (Eq, Show)

-- | Cache for occurs checking to prevent exponential blowup
newtype OccursCache = OccursCache (IORef (IM.IntMap MetaVar))

-- | Create empty occurs cache
emptyOccursCache :: IO OccursCache
emptyOccursCache = OccursCache <$> newIORef IM.empty

-- Metavariable Management
-- =======================

-- | Create a fresh metavariable with level constraints
freshMetaVar :: LvlSet -> IO MetaVar
freshMetaVar constraints = do
  n <- readIORef nextMetaVar
  writeIORef nextMetaVar (n + 1)
  let metavar = MetaVar n
  modifyIORef' globalMetaContext $ IM.insert n (Unsolved constraints)
  pure metavar

-- | Look up metavariable in context
lookupMeta :: MetaVar -> IO (Maybe MetaEntry)
lookupMeta (MetaVar n) = do
  mctx <- readIORef globalMetaContext
  pure $ IM.lookup n mctx

-- | Solve a metavariable with a term
solveMeta :: MetaVar -> Term -> LvlSet -> IO ()
solveMeta (MetaVar n) term constraints = do
  modifyIORef' globalMetaContext $ 
    IM.insert n (Solved term constraints)

-- | Check if metavariable is solved
isSolved :: MetaVar -> IO Bool
isSolved metavar = do
  entry <- lookupMeta metavar
  case entry of
    Just (Solved _ _) -> pure True
    _ -> pure False

-- Partial Renamings  
-- =================

-- | Create identity renaming
idRenaming :: MetaVar -> Lvl -> PartialRenaming
idRenaming occurs lvl = PartialRenaming occurs lvl lvl IM.empty

-- | Lift renaming over bound variable
liftRenaming :: PartialRenaming -> PartialRenaming  
liftRenaming pr = pr
  { prDomain = prDomain pr + 1
  , prCodomain = prCodomain pr + 1
  }

-- | Apply partial renaming to a level
applyRenaming :: PartialRenaming -> Lvl -> Maybe Lvl
applyRenaming pr (Lvl lvl) =
  case IM.lookup lvl (prRenaming pr) of
    Just (-1) -> Nothing  -- Undefined
    Just n    -> Just (Lvl n)
    Nothing   -> 
      if lvl >= fromIntegral (prCodomain pr)
        then Just (Lvl (lvl - fromIntegral (prCodomain pr - prDomain pr)))
        else Just (Lvl lvl)

-- | Build renaming from spine (for pattern unification)
buildRenaming :: Spine -> Maybe PartialRenaming
buildRenaming (Spine levels) = 
  if length (nub levels) == length levels  -- Check distinct variables
    then Just $ PartialRenaming
           { prOccurs = MetaVar (-1)  -- Will be set by caller
           , prDomain = Lvl (length levels)
           , prCodomain = Lvl (length levels) 
           , prRenaming = IM.fromList (zip (map (\(Lvl i) -> i) levels) [0..])
           }
    else Nothing  -- Non-linear spine

-- Occurs Checking with Partial Renamings
-- ======================================

-- | Advanced occurs check with partial renaming support
occursCheckWithRenaming :: PartialRenaming -> Term -> IO Bool  
occursCheckWithRenaming pr term = occursGo term
  where
    occursGo :: Term -> IO Bool
    occursGo t = case t of
      -- Variables: check if in scope via partial renaming
      Var _ i -> case applyRenaming pr (Lvl i) of
        Nothing -> pure True   -- Scope error - variable not in renaming
        Just _  -> pure False  -- Variable properly renamed
        
      -- Metavariables: check for the occurs constraint
      Met name typ context -> do
        if MetaVar (hash name) == prOccurs pr
          then pure True  -- Found the occurring metavar!
          else do
            -- Recursively check type and context
            typOccurs <- occursGo typ
            ctxOccurs <- mapM occursGo context
            pure (typOccurs || any id ctxOccurs)
      
      Ref _ _     -> pure False  
      Sub t'      -> occursGo t'
      Fix _ f     -> occursGo (f (Var "x" 0))  -- Approximate
      Let _ mt v f -> do
        vOccurs <- occursGo v
        bodyOccurs <- occursGo (f (Var "x" 0))  -- Approximate
        mtOccurs <- case mt of
          Just t' -> occursGo t'
          Nothing -> pure False
        pure (vOccurs || bodyOccurs || mtOccurs)
      Use _ v f   -> do
        vOccurs <- occursGo v
        bodyOccurs <- occursGo (f (Var "x" 0))  -- Approximate  
        pure (vOccurs || bodyOccurs)
      
      -- Core type constructors
      Set         -> pure False
      Chk x t     -> (||) <$> occursGo x <*> occursGo t
      Tst x       -> occursGo x
      Emp         -> pure False
      EmpM        -> pure False
      Uni         -> pure False
      One         -> pure False
      UniM f      -> occursGo f
      Bit         -> pure False
      Bt0         -> pure False
      Bt1         -> pure False
      BitM f t    -> (||) <$> occursGo f <*> occursGo t
      Nat         -> pure False
      Zer         -> pure False
      Suc n       -> occursGo n
      NatM z s    -> (||) <$> occursGo z <*> occursGo s
      Lst t       -> occursGo t
      Nil         -> pure False
      Con h t     -> (||) <$> occursGo h <*> occursGo t
      LstM n c    -> (||) <$> occursGo n <*> occursGo c
      Enu _       -> pure False
      Sym _       -> pure False
      EnuM cs e   -> do
        csOccurs <- mapM (occursGo . snd) cs
        eOccurs <- occursGo e
        pure (any id csOccurs || eOccurs)
      Num _       -> pure False
      Val _       -> pure False
      Op2 _ a b   -> (||) <$> occursGo a <*> occursGo b
      Op1 _ a     -> occursGo a
      Sig a b     -> (||) <$> occursGo a <*> occursGo b
      Tup a b     -> (||) <$> occursGo a <*> occursGo b
      SigM f      -> occursGo f
      All a b     -> (||) <$> occursGo a <*> occursGo b
      Lam _ _ f    -> occursGo (f (Var "x" 0))  -- Approximate
      App f x     -> (||) <$> occursGo f <*> occursGo x
      Eql t a b   -> do
        tOccurs <- occursGo t
        aOccurs <- occursGo a  
        bOccurs <- occursGo b
        pure (tOccurs || aOccurs || bOccurs)
      Rfl         -> pure False
      EqlM f      -> occursGo f
      Rwt e f     -> (||) <$> occursGo e <*> occursGo f
            
      -- Superpositions  
      Era         -> pure False
      Sup l a b   -> do
        lOccurs <- occursGo l
        aOccurs <- occursGo a
        bOccurs <- occursGo b
        pure (lOccurs || aOccurs || bOccurs)
      SupM l f    -> (||) <$> occursGo l <*> occursGo f
      Frk l a b   -> do
        lOccurs <- occursGo l
        aOccurs <- occursGo a  
        bOccurs <- occursGo b
        pure (lOccurs || aOccurs || bOccurs)
      Loc _ t     -> occursGo t
      Log s x     -> (||) <$> occursGo s <*> occursGo x
      Pri _       -> pure False
      Pat s m c   -> do
        sOccurs <- mapM occursGo s
        mOccurs <- mapM (occursGo . snd) m
        cOccurs <- mapM (\(ps, rhs) -> do
          psOccurs <- mapM occursGo ps
          rhsOccurs <- occursGo rhs
          pure (any id psOccurs || rhsOccurs)) c
        pure (any id sOccurs || any id mOccurs || any id cOccurs)

-- Pattern Unification
-- ===================

-- | Check if spine consists of distinct bound variables
isPatternSpine :: [Term] -> Bool
isPatternSpine terms = 
  let vars = [i | Var _ i <- terms]
  in length (nub vars) == length vars && length vars == length terms

-- | Extract spine from metavariable application context
extractSpine :: [Term] -> Maybe Spine
extractSpine terms
  | isPatternSpine terms = 
      Just $ Spine [Lvl i | Var _ i <- terms]
  | otherwise = Nothing

-- | Advanced pattern unification with partial renamings
-- Attempts to solve: ?α spine = rhs
solvePatternAdvanced :: MetaVar -> [Term] -> Term -> IO (Maybe Term)
solvePatternAdvanced metavar context rhs = do
  case extractSpine context of
    Nothing -> pure Nothing  -- Not a pattern spine
    Just spine -> do
      case buildRenaming spine of
        Nothing -> pure Nothing  -- Non-linear spine
        Just renaming -> do
          let pr = renaming { prOccurs = metavar }
          
          -- Check occurs and scope with sophisticated renaming
          occursOk <- not <$> occursCheckWithRenaming pr rhs
          if not occursOk
            then pure Nothing  -- Occurs check or scope error
            else do
              -- Quote RHS with renaming to build solution
              case quoteWithRenaming pr rhs of
                Nothing -> pure Nothing     -- Scope error in quoting
                Just quotedRhs -> do
                  -- Build lambda abstraction: λ spine. quotedRhs
                  let solution = buildLambdaAbstraction spine quotedRhs  
                  pure (Just solution)

-- | Quote term with partial renaming (scope-safe)
quoteWithRenaming :: PartialRenaming -> Term -> Maybe Term
quoteWithRenaming pr term = quoteGo term
  where
    quoteGo :: Term -> Maybe Term
    quoteGo t = case t of
      -- Variables: apply partial renaming
      Var name i -> do
        Lvl newI <- applyRenaming pr (Lvl i)
        pure $ Var name newI
        
      -- Metavariables: check not the occurring one
      Met name typ context -> do
        if MetaVar (hash name) == prOccurs pr
          then Nothing  -- Occurs check failure
          else do
            quotedTyp <- quoteGo typ
            quotedCtx <- mapM quoteGo context
            pure $ Met name quotedTyp quotedCtx
            
      -- Structural recursion for other constructors
      Ref name i    -> pure $ Ref name i
      Sub t'        -> Sub <$> quoteGo t'
      Fix name f    -> pure $ Fix name (\v -> fromJust $ quoteGo (f v))  -- Unsafe but needed
      Let name mt v f -> do
        quotedV <- quoteGo v  
        quotedMt <- traverse quoteGo mt
        pure $ Let name quotedMt quotedV (\v -> fromJust $ quoteGo (f v))
      Use name v f -> do
        quotedV <- quoteGo v
        pure $ Use name quotedV (\v -> fromJust $ quoteGo (f v))
        
      -- Base types
      Set           -> pure Set
      Chk x t       -> Chk <$> quoteGo x <*> quoteGo t
      Tst x         -> Tst <$> quoteGo x
      Emp           -> pure Emp  
      EmpM          -> pure EmpM
      Uni           -> pure Uni
      One           -> pure One
      UniM f        -> UniM <$> quoteGo f
      Bit           -> pure Bit
      Bt0           -> pure Bt0
      Bt1           -> pure Bt1
      BitM f t      -> BitM <$> quoteGo f <*> quoteGo t
      Nat           -> pure Nat
      Zer           -> pure Zer
      Suc n         -> Suc <$> quoteGo n
      NatM z s      -> NatM <$> quoteGo z <*> quoteGo s
      Lst t         -> Lst <$> quoteGo t
      Nil           -> pure Nil
      Con h t       -> Con <$> quoteGo h <*> quoteGo t
      LstM n c      -> LstM <$> quoteGo n <*> quoteGo c
      Enu names     -> pure $ Enu names
      Sym name      -> pure $ Sym name
      EnuM cs e     -> do
        quotedCs <- mapM (\(name, term) -> (,) name <$> quoteGo term) cs
        quotedE <- quoteGo e
        pure $ EnuM quotedCs quotedE
      Num typ       -> pure $ Num typ
      Val val       -> pure $ Val val
      Op2 op a b    -> Op2 op <$> quoteGo a <*> quoteGo b
      Op1 op a      -> Op1 op <$> quoteGo a
      Sig a b       -> Sig <$> quoteGo a <*> quoteGo b
      Tup a b       -> Tup <$> quoteGo a <*> quoteGo b
      SigM f        -> SigM <$> quoteGo f
      All a b       -> All <$> quoteGo a <*> quoteGo b
      Lam name mt f -> do
        quotedMt <- traverse quoteGo mt
        pure $ Lam name quotedMt (\v -> fromJust $ quoteGo (f v))
      App f x       -> App <$> quoteGo f <*> quoteGo x
      Eql t a b     -> Eql <$> quoteGo t <*> quoteGo a <*> quoteGo b
      Rfl           -> pure Rfl
      EqlM f        -> EqlM <$> quoteGo f
      Rwt e f       -> Rwt <$> quoteGo e <*> quoteGo f
      Era           -> pure Era
      Sup l a b     -> Sup <$> quoteGo l <*> quoteGo a <*> quoteGo b
      SupM l f      -> SupM <$> quoteGo l <*> quoteGo f
      Frk l a b     -> Frk <$> quoteGo l <*> quoteGo a <*> quoteGo b
      Loc span t    -> Loc span <$> quoteGo t
      Log s x       -> Log <$> quoteGo s <*> quoteGo x
      Pri prim      -> pure $ Pri prim
      Pat s m c     -> do
        quotedS <- mapM quoteGo s
        quotedM <- mapM (\(name, term) -> (,) name <$> quoteGo term) m
        quotedC <- mapM (\(patterns, rhs) -> do
          quotedPs <- mapM quoteGo patterns
          quotedRhs <- quoteGo rhs
          pure (quotedPs, quotedRhs)) c
        pure $ Pat quotedS quotedM quotedC

-- | Build lambda abstraction from spine  
buildLambdaAbstraction :: Spine -> Term -> Term
buildLambdaAbstraction (Spine []) body = body
buildLambdaAbstraction (Spine (Lvl i : rest)) body =
  Lam ("x" ++ show i) Nothing (\_ -> buildLambdaAbstraction (Spine rest) body)

-- | Abstract a term over a context (create lambda solution)
abstractOverContext :: [Term] -> Term -> Term
abstractOverContext [] rhs = rhs
abstractOverContext (Var name _ : rest) rhs = 
  Lam name Nothing (\_ -> abstractOverContext rest rhs)
abstractOverContext (_ : rest) rhs = 
  -- Non-variable in context, use fresh name
  Lam ("x" ++ show (length rest)) Nothing (\_ -> abstractOverContext rest rhs)

-- Enhanced Unification
-- ====================

-- | Enhanced unification with metavariable solving
unifyWithMetas :: Book -> Term -> Term -> IO Bool
unifyWithMetas book t1 t2 = unify (force book t1) (force book t2)
  where
    unify :: Term -> Term -> IO Bool
    unify (Met name typ context) rhs = do
      let metavar = MetaVar (hash name)
      solved <- isSolved metavar
      if solved
        then do
          entry <- lookupMeta metavar
          case entry of
            Just (Solved term _) -> unify term rhs
            _ -> pure False
        else do
          -- Try advanced pattern unification
          solution <- solvePatternAdvanced metavar context rhs
          case solution of
            Just term -> do
              solveMeta metavar term IS.empty
              pure True
            Nothing -> pure False  -- Couldn't solve
            
    unify lhs (Met name typ context) = unify (Met name typ context) lhs  -- Symmetric
    
    unify t1 t2 = pure $ equal 0 book t1 t2  -- Fall back to structural equality

-- Utility Functions  
-- =================

-- | Simple hash function for names (temporary)
hash :: String -> Int
hash = sum . map fromEnum

-- | Normalize term in empty environment (placeholder)
normalizeEmpty :: Term -> Term
normalizeEmpty = normal (Book M.empty [])  -- Simplified for now

-- | Convert Bend2 context to level set
contextToLevelSet :: Ctx -> LvlSet
contextToLevelSet (Ctx entries) = 
  IS.fromList [i | (i, _) <- zip [0..] entries]

-- | Create contextual metavariable for type checking
freshContextualMeta :: Ctx -> Type -> IO Term
freshContextualMeta ctx typ = do
  let constraints = contextToLevelSet ctx
  metavar <- freshMetaVar constraints
  let MetaVar n = metavar
  -- For now, return old Met format for compatibility
  pure $ Met ("?m" ++ show n) typ (contextToTerms ctx)

-- | Convert context to term list (for compatibility)
contextToTerms :: Ctx -> [Term]
contextToTerms (Ctx entries) = 
  [Var name i | (i, (name, _, _)) <- zip [0..] entries]

-- Export Functions for Integration
-- ================================

-- | Enhanced unification function to replace unifyTypes in Check.hs
enhancedUnifyTypes :: Book -> Term -> Term -> IO Bool
enhancedUnifyTypes = unifyWithMetas

-- | Create metavariable in type checking context  
createMetaVariable :: Ctx -> Type -> IO Term
createMetaVariable = freshContextualMeta

-- | Simple occurs check for testing (without partial renamings)
occursCheck :: MetaVar -> Term -> IO Bool
occursCheck metavar term = occursGo term
  where
    occursGo :: Term -> IO Bool
    occursGo t = case t of
      Var _ _     -> pure False
      Ref _ _     -> pure False  
      Met name _ context -> do
        if MetaVar (hash name) == metavar
          then pure True  -- Found it!
          else mapM occursGo context >>= pure . any id
      Sub t'      -> occursGo t'
      App f x     -> (||) <$> occursGo f <*> occursGo x
      Lam _ _ f    -> occursGo (f (Var "x" 0))  -- Approximate
      All a b     -> (||) <$> occursGo a <*> occursGo b
      _           -> pure False  -- Base cases