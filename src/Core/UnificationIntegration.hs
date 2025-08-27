{-# LANGUAGE ViewPatterns #-}

-- | Integration layer for enhanced metavariable unification
--
-- This module provides a compatibility layer to gradually integrate
-- the improved unification system into Bend2's existing type checker
-- without breaking existing functionality.

module Core.UnificationIntegration 
  ( -- * Enhanced unification functions
    enhancedUnifyTypes
  , createMetaVariable  
  , tryImprovedInference
  , isImprovedUnificationEnabled
  , enableImprovedUnification
  , disableImprovedUnification
  ) where

import Control.Monad (unless)
import Data.IORef
import System.IO.Unsafe (unsafePerformIO)

import Core.Type
import Core.Equal (equal)
import qualified Core.Unification as U
import qualified Data.IntSet as IS

-- | Global flag to enable/disable improved unification
{-# NOINLINE improvedUnificationEnabled #-}
improvedUnificationEnabled :: IORef Bool
improvedUnificationEnabled = unsafePerformIO (newIORef False)

-- | Check if improved unification is enabled
isImprovedUnificationEnabled :: IO Bool
isImprovedUnificationEnabled = readIORef improvedUnificationEnabled

-- | Enable improved unification system
enableImprovedUnification :: IO ()
enableImprovedUnification = writeIORef improvedUnificationEnabled True

-- | Disable improved unification system (fall back to old system)
disableImprovedUnification :: IO ()  
disableImprovedUnification = writeIORef improvedUnificationEnabled False

-- | Enhanced unification that falls back to old system if needed
enhancedUnifyTypes :: Book -> Term -> Term -> IO Bool
enhancedUnifyTypes book t1 t2 = do
  enabled <- isImprovedUnificationEnabled
  if enabled
    then do
      -- Try new unification system
      result <- U.enhancedUnifyTypes book t1 t2
      if result 
        then pure True
        else -- Fall back to old system if new system fails
          pure $ equal 0 book t1 t2
    else
      -- Use old system
      pure $ equal 0 book t1 t2

-- | Smart metavariable creation that uses improved system when available
createMetaVariable :: Ctx -> Type -> IO Term  
createMetaVariable ctx typ = do
  enabled <- isImprovedUnificationEnabled
  if enabled
    then U.createMetaVariable ctx typ
    else do
      -- Fall back to creating old-style Met terms
      let metaName = "?fallback" ++ show (length (getCtxEntries ctx))
          context = contextToTerms ctx
      pure $ Met metaName typ context
  where
    getCtxEntries (Ctx entries) = entries
    contextToTerms (Ctx entries) = 
      [Var name i | (i, (name, _, _)) <- zip [0..] entries]

-- | Try improved type inference for cases where old system fails
tryImprovedInference :: Int -> Span -> Book -> Ctx -> Term -> Result Term -> IO (Result Term)
tryImprovedInference d span book ctx term oldResult = do
  enabled <- isImprovedUnificationEnabled
  case oldResult of
    Fail (CantInfer {}) | enabled -> do
      -- Old system failed with CantInfer, try improved system
      tryWithImprovedMetas term
    _ -> 
      -- Either not enabled or old system succeeded
      pure oldResult
  where
    tryWithImprovedMetas :: Term -> IO (Result Term)
    tryWithImprovedMetas t = case t of
      -- Look for cases where we can create better metavariables
      Lam name Nothing body -> do
        -- Create contextual metavariable for missing type annotation
        paramTy <- U.createMetaVariable ctx Set
        pure $ Done (All paramTy (Lam name (Just paramTy) body))
        
      App f x -> do
        -- Try to infer function type with improved unification
        -- This is a simplified version - full implementation would be more sophisticated
        funTy <- U.createMetaVariable ctx Set
        argTy <- U.createMetaVariable ctx Set  
        resTy <- U.createMetaVariable ctx Set
        let expectedFunTy = All argTy (Lam "x" (Just argTy) (\_ -> resTy))
        
        -- Try to unify with improved system
        unifyOk <- U.enhancedUnifyTypes book funTy expectedFunTy
        if unifyOk
          then pure $ Done resTy
          else pure oldResult
          
      _ -> pure oldResult

-- | Wrapper for Check.hs integration - enhanced infer function
enhancedInfer :: Int -> Span -> Book -> Ctx -> Term -> IO (Result Term)
enhancedInfer d span book ctx term = do
  -- First try the old system
  let oldResult = infer d span book ctx term
  case oldResult of
    result@(Done _) -> pure result  -- Old system succeeded
    failResult -> do
      -- Old system failed, try improved inference
      tryImprovedInference d span book ctx term failResult

-- | Helper to safely convert synchronous Result to IO Result
liftResult :: Result a -> IO (Result a)
liftResult = pure

-- Compatibility functions for gradual integration
-- ===============================================

-- | Gradually migrate Met constructor usage
migrateMet :: Term -> IO Term
migrateMet (Met name typ context) = do
  enabled <- isImprovedUnificationEnabled
  if enabled
    then do
      -- Convert to improved metavar system
      let constraints = extractConstraints context
      metavar <- U.freshMetaVar constraints
      let U.MetaVar n = metavar
      pure $ Met ("?m" ++ show n) typ context  -- Keep same format for compatibility
    else 
      pure $ Met name typ context  -- No change
  where
    extractConstraints :: [Term] -> U.LvlSet
    extractConstraints terms = 
      IS.fromList [i | Var _ i <- terms]
      
migrateMet term = pure term

-- | Update all Met constructors in a term
migrateAllMets :: Term -> IO Term
migrateAllMets term = case term of
  Met {} -> migrateMet term
  Sub t -> Sub <$> migrateAllMets t
  Fix name f -> pure $ Fix name (\v -> unsafePerformIO $ migrateAllMets (f v))
  Let name mt v f -> do
    migratedV <- migrateAllMets v
    migratedMt <- traverse migrateAllMets mt
    pure $ Let name migratedMt migratedV (\v -> unsafePerformIO $ migrateAllMets (f v))
  Use name v f -> do
    migratedV <- migrateAllMets v  
    pure $ Use name migratedV (\v -> unsafePerformIO $ migrateAllMets (f v))
  Chk x t -> Chk <$> migrateAllMets x <*> migrateAllMets t
  Tst x -> Tst <$> migrateAllMets x
  UniM f -> UniM <$> migrateAllMets f
  BitM f t -> BitM <$> migrateAllMets f <*> migrateAllMets t
  Suc n -> Suc <$> migrateAllMets n
  NatM z s -> NatM <$> migrateAllMets z <*> migrateAllMets s
  Lst t -> Lst <$> migrateAllMets t
  Con h t -> Con <$> migrateAllMets h <*> migrateAllMets t
  LstM n c -> LstM <$> migrateAllMets n <*> migrateAllMets c
  EnuM cs e -> do
    migratedCs <- mapM (\(name, term) -> (,) name <$> migrateAllMets term) cs
    migratedE <- migrateAllMets e  
    pure $ EnuM migratedCs migratedE
  Op2 op a b -> Op2 op <$> migrateAllMets a <*> migrateAllMets b
  Op1 op a -> Op1 op <$> migrateAllMets a
  Sig a b -> Sig <$> migrateAllMets a <*> migrateAllMets b
  Tup a b -> Tup <$> migrateAllMets a <*> migrateAllMets b
  SigM f -> SigM <$> migrateAllMets f
  All a b -> All <$> migrateAllMets a <*> migrateAllMets b
  Lam name mt f -> do
    migratedMt <- traverse migrateAllMets mt
    pure $ Lam name migratedMt (\v -> unsafePerformIO $ migrateAllMets (f v))
  App f x -> App <$> migrateAllMets f <*> migrateAllMets x
  Eql t a b -> Eql <$> migrateAllMets t <*> migrateAllMets a <*> migrateAllMets b
  EqlM f -> EqlM <$> migrateAllMets f
  Rwt e f -> Rwt <$> migrateAllMets e <*> migrateAllMets f
  Sup l a b -> Sup <$> migrateAllMets l <*> migrateAllMets a <*> migrateAllMets b
  SupM l f -> SupM <$> migrateAllMets l <*> migrateAllMets f
  Frk l a b -> Frk <$> migrateAllMets l <*> migrateAllMets a <*> migrateAllMets b
  Loc span t -> Loc span <$> migrateAllMets t
  Log s x -> Log <$> migrateAllMets s <*> migrateAllMets x
  Pat s m c -> do
    migratedS <- mapM migrateAllMets s
    migratedM <- mapM (\(name, term) -> (,) name <$> migrateAllMets term) m
    migratedC <- mapM (\(patterns, rhs) -> do
      migratedPs <- mapM migrateAllMets patterns
      migratedRhs <- migrateAllMets rhs
      pure (migratedPs, migratedRhs)) c  
    pure $ Pat migratedS migratedM migratedC
  _ -> pure term  -- Base cases (literals, etc.)

-- Helper to import current infer function (this would need to be updated in Check.hs)
infer :: Int -> Span -> Book -> Ctx -> Term -> Result Term
infer = error "This should be imported from Core.Check, but we need to avoid circular imports"