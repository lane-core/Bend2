{-./Type.hs-}

{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE ViewPatterns #-}

-- Pattern Matching Flattener
-- ==========================
-- 
-- This algorithm converts pattern matching expressions with multiple 
-- scrutinees into nested case trees with single scrutinees. Example:
--
-- match x y
-- | 0n     0n          = X0
-- | (1n+x) 0n          = X1
-- | 0n     (1n+y)      = X2
-- | (1n+x) (1n+0n)     = X3
-- | (1n+x) (1n+(1n+z)) = X4
-- ------------------------- flatten
-- match x:
--   case 0n:
--     match y:
--       case 0n: X0
--       case 1+y: X2
--   case 1n+x:
--     match y:
--       case 0n: X1
--       case 1n+y_:
--         match y_:
--           case 0n: X3
--           case 1n+z: X4

module Core.Flatten where

import Data.List (nub, find)
import qualified Data.Map as M

import Debug.Trace

import Core.Type

-- Main Flattener
-- --------------

flatten :: Int -> Term -> Term
flatten d (Var n i)   = Var n i
flatten d (Ref n)     = Ref n
flatten d (Sub t)     = Sub (flatten d t)
flatten d (Fix n f)   = Fix n (\x -> flatten (d+1) (f x))
flatten d (Let v f)   = Let (flatten d v) (flatten d f)
flatten d Set         = Set
flatten d (Ann x t)   = Ann (flatten d x) (flatten d t)
flatten d (Chk x t)   = Chk (flatten d x) (flatten d t)
flatten d Emp         = Emp
flatten d Efq         = Efq
flatten d Uni         = Uni
flatten d One         = One
flatten d (Use f)     = Use (flatten d f)
flatten d Bit         = Bit
flatten d Bt0         = Bt0
flatten d Bt1         = Bt1
flatten d (Bif f t)   = Bif (flatten d f) (flatten d t)
flatten d Nat         = Nat
flatten d Zer         = Zer
flatten d (Suc n)     = Suc (flatten d n)
flatten d (Swi z s)   = Swi (flatten d z) (flatten d s)
flatten d (Lst t)     = Lst (flatten d t)
flatten d Nil         = Nil
flatten d (Con h t)   = Con (flatten d h) (flatten d t)
flatten d (Mat n c)   = Mat (flatten d n) (flatten d c)
flatten d (Enu s)     = Enu s
flatten d (Sym s)     = Sym s
flatten d (Cse c e)   = Cse [(s, flatten d t) | (s, t) <- c] (flatten d e)
flatten d (Sig a b)   = Sig (flatten d a) (flatten d b)
flatten d (Tup a b)   = Tup (flatten d a) (flatten d b)
flatten d (Get f)     = Get (flatten d f)
flatten d (All a b)   = All (flatten d a) (flatten d b)
flatten d (Lam n f)   = Lam n (\x -> flatten (d+1) (f x))
flatten d (App f x)   = App (flatten d f) (flatten d x)
flatten d (Eql t a b) = Eql (flatten d t) (flatten d a) (flatten d b)
flatten d Rfl         = Rfl
flatten d (Rwt f)     = Rwt (flatten d f)
flatten d (Met i t x) = Met i (flatten d t) (map (flatten d) x)
flatten d (Ind t)     = Ind (flatten d t)
flatten d (Frz t)     = Frz (flatten d t)
flatten d Era         = Era
flatten d (Sup l a b) = Sup l (flatten d a) (flatten d b)
flatten d (Num t)     = Num t
flatten d (Val v)     = Val v
flatten d (Op2 o a b) = Op2 o (flatten d a) (flatten d b)
flatten d (Op1 o a)   = Op1 o (flatten d a)
flatten d (Pri p)     = Pri p
flatten d (Loc s t)   = Loc s (flatten d t)
flatten d (Pat s m c) = finish $ flat d (Pat s m c)

flattenBook :: Book -> Book
flattenBook (Book defs) = Book (M.map flattenDefn defs)
  where flattenDefn (i, x, t) = (i, flatten 0 x, flatten 0 t)

-- Pattern Match Flattening
-- ------------------------

flat :: Int -> Term -> Term
flat d pat@(Pat (s:ss) ms ((((strip->Var k i):ps),rhs):cs)) =
  trace (">> var: " ++ show pat) $
  Pat ss ((k,s):ms) (abst (d+1) k (((Var k i:ps),rhs):cs))
flat d pat@(Pat (s:ss) ms cs@((((strip->p):_),_):_)) =
  trace (">> ctr: " ++ show pat) $
  Pat [s] moves [([ct], picks), ([var d], drops)] where
    (ct,fs) = ctrOf d p
    (ps,ds) = peel ct cs
    moves   = ms ++ map (\ (s,i) -> (patOf (d+i) s, s)) (zip ss [0..])
    picks   = flatten d' (Pat (fs   ++ ss) ms ps) where d' = d + length fs
    drops   = flatten d' (Pat (var d : ss) ms ds) where d' = d + 1
flat d pat = pat

-- Converts an all-variable column to a 'with' statement
-- match x y { case x0 @A: F(x0) ; case x1 @B: F(x1) }
-- --------------------------------------------------- abst k
-- match y { with k=x case @A: F(k) ; case @B: F(k) }
abst :: Int -> Name -> [Case] -> [Case]
abst d k ((((strip->Var j _):ps),rhs):cs) = (ps, subst j (Var k 0) rhs) : abst d k cs
abst d k ((((strip->ctr    ):ps),rhs):cs) = error "redundant-pattern"
abst d k cs                               = cs

-- Peels a constructor layer from a column
-- match x y { case @Z{} @A: A ; case @S{@Z} @B: B ; case @S{@S{p}} @C: C(p) }
-- --------------------------------------------------------------------------- peel @Z , peel @S{k}
-- match x:
--   with y
--   case @Z: match y { case @A: A }
--   case @S{k}: match k y { case @Z @B: B ; case @S{p} @C: C(p) }
peel :: Term -> [Case] -> ([Case],[Case])
peel (strip->k) ((((strip->p):ps),rhs):cs) = case (k,p) of
  (Zer   , Zer  ) -> ((ps    ,rhs) : picks , drops)
  (Suc _ , Suc x) -> (((x:ps),rhs) : picks , drops)
  x               -> (picks , ((p:ps),rhs) : drops)
  where (picks, drops) = peel k cs
peel k cs = (cs,cs)

-- Utils
-- -----

-- Substitutes a move list into an expression
shove :: [Move] -> Term -> Term
shove ms term = foldr (\ (k,v) x -> subst k v x) term ms 

-- Converts zero-scrutinee matches to plain expressions
-- match { with x=A . case: F(x,.) }
-- --------------------------------- decay
-- F(A,.)
decay :: Term -> Term
decay (Pat [] ms [([],rhs)]) = decay (shove ms rhs)
decay term                   = term

-- Merges redundant case-match chains into parent
-- match . { . case x: match x { case A:A ; case B:B . } . }
-- --------------------------------------------------------- merge
-- match . { . case A:A ; case B:B . }
merge :: Term -> Term
merge (Pat ss ms cs) = Pat ss ms (cases cs) where 
  cases :: [Case] -> [Case]
  cases (([Var x _], (Pat [Var x' _] ms cs')) : cs)
    | x == x' = csA ++ csB
    where csA = map (\ (p,rhs) -> (p, merge (shove ms rhs))) cs'
          csB = cases cs
  cases ((p,rhs):cs) = (p, merge rhs) : cases cs
  cases []           = []
merge term = term

finish :: Term -> Term
finish = merge . decay

-- Helpers
-- -------

-- Creates a fresh name at given depth
fresh :: Int -> String
fresh d = "x" ++ show d

-- Creates a fresh variable at given depth
var :: Int -> Term
var d = Var (fresh d) d

-- Creates a fresh pattern at given depth
pat :: Int -> Term -> Term
pat d f = Var (patOf d f) d

-- Gets a var name, or creates a fresh one
patOf :: Int -> Term -> String
patOf d (strip->Var k i) = k
patOf d p                = fresh d

-- Returns a single-layer constructor, replacing fields by pattern variables
ctrOf :: Int -> Term -> (Term, [Term])
ctrOf d Zer     = (Zer , [])
ctrOf d (Suc p) = (Suc (pat d p), [pat d p])
ctrOf d x       = (var d , [var d])

-- Subst a var for a value in a term
subst :: Name -> Term -> Term -> Term
subst name val term = trace ("-- subst " ++ name ++ " → " ++ show val ++ " | " ++ show term) $ case term of
  Var k _   -> if k == name then trace "OK" val else trace "NO" term
  Ref k     -> Ref k
  Sub t     -> Sub (subst name val t)
  Fix k f   -> Fix k (\x -> subst name val (f x))
  Let v f   -> Let (subst name val v) (subst name val f)
  Ann x t   -> Ann (subst name val x) (subst name val t)
  Chk x t   -> Chk (subst name val x) (subst name val t)
  Set       -> Set
  Emp       -> Emp
  Efq       -> Efq
  Uni       -> Uni
  One       -> One
  Use f     -> Use (subst name val f)
  Bit       -> Bit
  Bt0       -> Bt0
  Bt1       -> Bt1
  Bif f t   -> Bif (subst name val f) (subst name val t)
  Nat       -> Nat
  Zer       -> Zer
  Suc n     -> Suc (subst name val n)
  Swi z s   -> Swi (subst name val z) (subst name val s)
  Lst t     -> Lst (subst name val t)
  Nil       -> Nil
  Con h t   -> Con (subst name val h) (subst name val t)
  Mat n c   -> Mat (subst name val n) (subst name val c)
  Enu s     -> Enu s
  Sym s     -> Sym s
  Cse c e   -> Cse [(s, subst name val t) | (s, t) <- c] (subst name val e)
  Sig a b   -> Sig (subst name val a) (subst name val b)
  Tup a b   -> Tup (subst name val a) (subst name val b)
  Get f     -> Get (subst name val f)
  All a b   -> All (subst name val a) (subst name val b)
  Lam k f   -> Lam k (\x -> subst name val (f x))
  App f x   -> App (subst name val f) (subst name val x)
  Eql t a b -> Eql (subst name val t) (subst name val a) (subst name val b)
  Rfl       -> Rfl
  Rwt f     -> Rwt (subst name val f)
  Met i t x -> Met i (subst name val t) (map (subst name val) x)
  Ind t     -> Ind (subst name val t)
  Frz t     -> Frz (subst name val t)
  Era       -> Era
  Sup l a b -> Sup l (subst name val a) (subst name val b)
  Num t     -> Num t
  Val v     -> Val v
  Op2 o a b -> Op2 o (subst name val a) (subst name val b)
  Op1 o a   -> Op1 o (subst name val a)
  Pri p     -> Pri p
  Loc s t   -> Loc s (subst name val t)
  Pat s m c -> Pat (map (subst name val) s) m (map substCase c)
    where substCase (pats, rhs) = (map (subst name val) pats, subst name val rhs)
