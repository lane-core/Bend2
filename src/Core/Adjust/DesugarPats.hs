{-# LANGUAGE ViewPatterns #-}

-- Pattern Desugaring
-- ==================
-- Converts all Pats to native expression-based matches.

module Core.Adjust.DesugarPats where

import Core.Bind
import Core.Show
import Core.Type
import Core.WHNF
import qualified Data.Set as S

desugarPats :: Int -> Term -> Term
desugarPats d (Var n i)       = Var n i
desugarPats d (Ref n i)       = Ref n i
desugarPats d (Sub t)         = Sub (desugarPats d t)
desugarPats d (Fix n f)       = Fix n (\x -> desugarPats (d+1) (f x))
desugarPats d (Let k t v f)   = Let k (fmap (desugarPats d) t) (desugarPats d v) (\x -> desugarPats (d+1) (f x))
desugarPats d (Use k v f)     = Use k (desugarPats d v) (\x -> desugarPats (d+1) (f x))
desugarPats d Set             = Set
desugarPats d (Chk x t)       = Chk (desugarPats d x) (desugarPats d t)
desugarPats d Emp             = Emp
desugarPats d EmpM            = EmpM
desugarPats d Uni             = Uni
desugarPats d One             = One
desugarPats d (UniM f)        = UniM (desugarPats d f)
desugarPats d Bit             = Bit
desugarPats d Bt0             = Bt0
desugarPats d Bt1             = Bt1
desugarPats d (BitM f t)      = BitM (desugarPats d f) (desugarPats d t)
desugarPats d Nat             = Nat
desugarPats d Zer             = Zer
desugarPats d (Suc n)         = Suc (desugarPats d n)
desugarPats d (NatM z s)      = NatM (desugarPats d z) (desugarPats d s)
desugarPats d (Lst t)         = Lst (desugarPats d t)
desugarPats d Nil             = Nil
desugarPats d (Con h t)       = Con (desugarPats d h) (desugarPats d t)
desugarPats d (LstM n c)      = LstM (desugarPats d n) (desugarPats d c)
desugarPats d (Enu s)         = Enu s
desugarPats d (Sym s)         = Sym s
desugarPats d (EnuM c e)      = EnuM [(s, desugarPats d t) | (s, t) <- c] (desugarPats d e)
desugarPats d (Sig a b)       = Sig (desugarPats d a) (desugarPats d b)
desugarPats d (Tup a b)       = Tup (desugarPats d a) (desugarPats d b)
desugarPats d (SigM f)        = SigM (desugarPats d f)
desugarPats d (All a b)       = All (desugarPats d a) (desugarPats d b)
desugarPats d (Lam n t f)     = Lam n (fmap (desugarPats d) t) (\x -> desugarPats (d+1) (f x))
desugarPats d (App f x)       = App (desugarPats d f) (desugarPats d x)
desugarPats d (Eql t a b)     = Eql (desugarPats d t) (desugarPats d a) (desugarPats d b)
desugarPats d Rfl             = Rfl
desugarPats d (EqlM f)        = EqlM (desugarPats d f)
desugarPats d (Met i t x)     = Met i (desugarPats d t) (map (desugarPats d) x)
desugarPats d Era             = Era
desugarPats d (Sup l a b)     = Sup (desugarPats d l) (desugarPats d a) (desugarPats d b)
desugarPats d (SupM l f)      = SupM (desugarPats d l) (desugarPats d f)
desugarPats d (Frk l a b)     = Frk (desugarPats d l) (desugarPats d a) (desugarPats d b)
desugarPats d (Rwt e f)       = Rwt (desugarPats d e) (desugarPats d f)
desugarPats d (Num t)         = Num t
desugarPats d (Val v)         = Val v
desugarPats d (Op2 o a b)     = Op2 o (desugarPats d a) (desugarPats d b)
desugarPats d (Op1 o a)       = Op1 o (desugarPats d a)
desugarPats d (Pri p)         = Pri p
desugarPats d (Log s x)       = Log (desugarPats d s) (desugarPats d x)
desugarPats d (Loc s t)       = Loc s (desugarPats d t)
desugarPats d (Pat [s] ms cs) = match d s ms cs
desugarPats d (Pat ss  ms []) = One
desugarPats d (Pat ss  ms cs) = error "desugarPats: multiple scrutinees after flattening"

match :: Int -> Term -> [Move] -> [Case] -> Term

-- match x { 0n: z ; 1n+p: s }
-- ---------------------------
-- ~x { 0n: z ; 1n+: λp. s }
match d x ms (([(cut -> Zer)], z) : ([(cut -> Suc p)], s) : _) =
  apps d (map snd ms) $ App (NatM if_zer if_suc) x
  where if_zer = lam d (map fst ms) $ desugarPats d z
        if_suc = Lam (patOf d p) (Just Nat) $ \x -> lam d (map fst ms) $ desugarPats (d+1) s

-- match x { 1n+p: s ; 0n: z }
-- ---------------------------
-- ~x { 0n: z ; 1n+: λp. s }
match d x ms (([(cut -> Suc p)], s) : ([(cut -> Zer)], z) : _) =
  apps d (map snd ms) $ App (NatM if_zer if_suc) x
  where if_zer = lam d (map fst ms) $ desugarPats d z
        if_suc = Lam (patOf d p) (Just Nat) $ \x -> lam d (map fst ms) $ desugarPats (d+1) s

-- match x { 0n: z ; k: v }
-- --------------------------------------
-- ~x { 0n: z ; 1n+: λk. v[k := 1n+k] }
match d x ms (([(cut -> Zer)], z) : ([(cut -> Var k i)], v) : _) =
  apps d (map snd ms) $ App (NatM if_zer if_suc) x
  where if_zer = lam d (map fst ms) $ desugarPats d z
        if_suc = Lam k (Just Nat) $ \x -> lam d (map fst ms) $ desugarPats (d+1) (bindVarByName k (Suc (Var k 0)) v)

-- match x { 1n+p: s ; k: v }
-- ------------------------------------
-- ~x { 0n: v[k := 0n] ; 1n+: λp. s }
match d x ms (([(cut -> Suc p)], s) : ([(cut -> Var k i)], v) : _) =
  apps d (map snd ms) $ App (NatM if_zer if_suc) x
  where if_zer = lam d (map fst ms) $ desugarPats d (bindVarByName k Zer v)
        if_suc = Lam (patOf d p) (Just Nat) $ \x -> lam d (map fst ms) $ desugarPats (d+1) s

-- match x { False: f ; True: t }
-- ------------------------------
-- ~x { False: f ; True: t }
match d x ms (([(cut -> Bt0)], f) : ([(cut -> Bt1)], t) : _) =
  apps d (map snd ms) $ App (BitM (lam d (map fst ms) $ desugarPats d f) (lam d (map fst ms) $ desugarPats d t)) x

-- match x { True: t ; False: f }
-- ------------------------------
-- ~x { False: f ; True: t }
match d x ms (([(cut -> Bt1)], t) : ([(cut -> Bt0)], f) : _) =
  apps d (map snd ms) $ App (BitM (lam d (map fst ms) $ desugarPats d f) (lam d (map fst ms) $ desugarPats d t)) x

-- match x { False: f ; k: v }
-- --------------------------------------
-- ~x { False: f ; True: v[k := True] }
match d x ms (([(cut -> Bt0)], f) : ([(cut -> Var k i)], v) : _) =
  apps d (map snd ms) $ App (BitM (lam d (map fst ms) $ desugarPats d f) (lam d (map fst ms) $ desugarPats d (bindVarByName k Bt1 v))) x

-- match x { True: t ; k: v }
-- ---------------------------------------
-- ~x { False: v[k := False] ; True: t }
match d x ms (([(cut -> Bt1)], t) : ([(cut -> Var k i)], v) : _) =
  apps d (map snd ms) $ App (BitM (lam d (map fst ms) $ desugarPats d (bindVarByName k Bt0 v)) (lam d (map fst ms) $ desugarPats d t)) x

-- match x { []: n ; h<>t: c }
-- ------------------------------
-- ~x { []: n ; <>: λh. λt. c }
match d x ms (([(cut -> Nil)], n) : ([(cut -> Con h t)], c) : _) =
  apps d (map snd ms) $ App (LstM if_nil if_con) x
  where if_nil = lam d (map fst ms) $ desugarPats d n
        if_con = Lam (patOf d h) Nothing $ \_ -> Lam (patOf (d+1) t) Nothing $ \_ -> lam d (map fst ms) $ desugarPats (d+2) c

-- match x { h<>t: c ; []: n }
-- ------------------------------
-- ~x { []: n ; <>: λh. λt. c }
match d x ms (([(cut -> Con h t)], c) : ([(cut -> Nil)], n) : _) =
  apps d (map snd ms) $ App (LstM if_nil if_con) x
  where if_nil = lam d (map fst ms) $ desugarPats d n
        if_con = Lam (patOf d h) Nothing $ \_ -> Lam (patOf (d+1) t) Nothing $ \_ -> lam d (map fst ms) $ desugarPats (d+2) c

-- match x { []: n ; k: v }
-- -----------------------------------------
-- ~x { []: n ; <>: λh. λt. v[k := h<>t] }
match d x ms (([(cut -> Nil)], n) : ([(cut -> Var k i)], v) : _) =
  apps d (map snd ms) $ App (LstM if_nil if_con) x
  where if_nil = lam d (map fst ms) $ desugarPats d n
        if_con = Lam (nam d) Nothing $ \_ -> Lam (nam (d+1)) Nothing $ \_ -> lam d (map fst ms) $ desugarPats (d+2) (bindVarByName k (Con (var d) (var (d+1))) v)

-- match x { h<>t: c ; k: v }
-- ---------------------------------------
-- ~x { []: v[k := []] ; <>: λh. λt. c }
match d x ms (([(cut -> Con h t)], c) : ([(cut -> Var k i)], v) : _) =
  apps d (map snd ms) $ App (LstM if_nil if_con) x
  where if_nil = lam d (map fst ms) $ desugarPats d (bindVarByName k Nil v)
        if_con = Lam (patOf d h) Nothing $ \_ -> Lam (patOf (d+1) t) Nothing $ \_ -> lam d (map fst ms) $ desugarPats (d+2) c

-- match x { (): u }
-- -----------------
-- ~x { (): u }
match d x ms cs@(([(cut -> One)], u) : _) =
  apps d (map snd ms) $ App (UniM (lam d (map fst ms) $ desugarPats d u)) x

-- match x { (a,b): p }
-- --------------------
-- ~x { (,): λa. λb. p }
match d x ms (([(cut -> Tup a b)], p) : _) =
  apps d (map snd ms) $ App (SigM if_tup) x
  where if_tup = Lam (patOf d a) Nothing $ \_ -> Lam (patOf (d+1) b) Nothing $ \_ -> lam d (map fst ms) $ desugarPats (d+2) p

-- match x { @S1: b1 ; @S2: b2 ; ... ; k: d }
-- ------------------------------------------
-- ~x { @S1:b1 ; @S2:b2 ; ... ; d }
match d x ms cs@(([(cut -> Sym _)], _) : _) =
  let (cBranches, defBranch) = collect cs
  in apps d (map snd ms) $ App (EnuM cBranches defBranch) x
  where
    collect :: [Case] -> ([(String, Term)], Term)
    collect [] = ([], Lam "_" Nothing $ \_ -> lam d (map fst ms) $ One)
    collect (([(cut -> Sym s)], rhs) : rest) =
      let (cs, def) = collect rest
      in ((s, lam d (map fst ms) $ desugarPats d rhs) : cs, def)
    collect (([(cut -> Var k _)], rhs) : _) =
      ([], Lam k Nothing $ \_ -> lam d (map fst ms) $ desugarPats (d+1) rhs)
    collect (c:_) = error $ "match:invalid-Sym-case:" ++ show c

-- match x { &L{a,b}: s }
-- ---------------------------
-- ~ x { &L{,}: λa. λb. s }
match d x ms (([(cut -> Sup l a b)], s) : _) =
  apps d (map snd ms) $ App (SupM l if_sup) x
  where if_sup = Lam (patOf d a) Nothing $ \_ -> Lam (patOf (d+1) b) Nothing $ \_ -> lam d (map fst ms) $ desugarPats (d+2) s

-- match x { Rfl: r }
-- ------------------
-- ~x { Rfl: r }
match d x ms (([(cut -> Rfl)], r) : _) =
  apps d (map snd ms) $ App (EqlM (lam d (map fst ms) $ desugarPats d r)) x

-- match x { k: body }
-- -------------------
-- body[k := x]
match d x ms (([(cut -> Var k i)], body) : _) =
  lam d (map fst ms) $ desugarPats d (shove d ((k, x) : ms) body)

-- match x { }
-- -----------
-- λ{}
match d x ms [] =
  apps d (map snd ms) (App EmpM x)

-- Invalid pattern
match d s ms cs = error $ "match - invalid pattern: " ++ show (d, s, ms, cs)

-- Helper function to create lambda abstractions
lam :: Int -> [Name] -> Term -> Term
lam d []     t = t
lam d (k:ks) t = Lam k Nothing $ \_ -> lam (d+1) ks t

-- Applies n arguments to a value
apps :: Int -> [Term] -> Term -> Term
apps d ms t = foldl (\t x -> App t x) t ms

-- Substitutes a move list into an expression
shove :: Int -> [Move] -> Term -> Term
shove d ms term = foldr (\ (k,v) x -> bindVarByName k v x) term ms

-- Creates a fresh name at given depth
nam :: Int -> String
nam d = "_x" ++ show d

-- Creates a fresh variable at given depth
var :: Int -> Term
var d = Var (nam d) d

-- Gets a var name, or creates a fresh one
patOf :: Int -> Term -> String
patOf d (cut->Var k i) = k
patOf d p              = nam d
