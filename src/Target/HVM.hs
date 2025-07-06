{-./../Core/Type.hs-}

{-# LANGUAGE ViewPatterns #-}

module Target.HVM where

import Core.Type
import Data.List (isInfixOf, unsnoc)
import Debug.Trace
import qualified Data.Map as M
import qualified Data.Map.Strict as MS
import qualified HVM.Type as HVM

compile :: Book -> String
compile (Book defs) =
  let fns = map compileFn (M.toList defs)
  in prelude ++ unlines fns

prelude :: String
prelude = unlines [
    "// Prelude",
    "// -------",
    "data List { #Nil #Cons{head tail} }",
    "data Bit { #B0 #B1 }",
    "data Nat { #Z #S{n} }",
    "data Pair { #P{fst snd} }",
    "@fix(&f x) = (f @fix(f x))",
    "",
    "// Bend to HVM Compiler Output",
    "// ---------------------------",
    ""
  ]

compileFn :: (String, Defn) -> String
compileFn (name, (_, tm, ty)) = "@" ++ name ++ "$" ++ " = " ++ HVM.showCore (fnToHVM name tm ty)

fnToHVM :: String -> Term -> Type -> HVM.Core
fnToHVM name tm ty
  -- TODO: Type definitions
  | (Just _) <- getCtrDef = typeToHVM tm
  -- TODO: Function arguments
  | otherwise = termToHVM MS.empty tm
  where
    getCtrDef = undefined

termToHVM :: MS.Map String String -> Term -> HVM.Core
termToHVM ctx tm = go tm where
  subst a f = f (Var a 0)

  go (Var n i) =
    case MS.lookup n ctx of
      Just n  -> HVM.Var n
      Nothing -> HVM.Var (n++"$") 
  go (Ref k)      = HVM.Ref (k++"$") 0 [] -- TODO: Ref arguments
  go (Sub t)      = termToHVM ctx t
  go (Fix n f)    = HVM.Ref "fix" 0 [HVM.Lam ("&"++n++"$") (termToHVM (MS.insert n (n++"$") ctx) (f (Var n 0)))]
  go (Let v f)    = HVM.App (termToHVM ctx f) (termToHVM ctx v)
  go Set          = HVM.Era
  go (Chk v t)    = termToHVM ctx v
  go Emp          = HVM.Era
  go (EmpM x)     = HVM.Era
  go Uni          = HVM.Era
  go One          = HVM.U32 1
  go (UniM x f)   = termToHVM ctx f
  go Bit          = HVM.Era
  go Bt0          = HVM.Ctr "#B0" []
  go Bt1          = HVM.Ctr "#B1" []
  go (BitM x f t) = HVM.Mat (HVM.MAT 0) (termToHVM ctx x) [] [("#B0", [], termToHVM ctx f), ("#B1", [], termToHVM ctx t)]
  go Nat          = HVM.Era
  go Zer          = HVM.Ctr "#Z" []
  go (Suc p)      = HVM.Ctr "#S" [termToHVM ctx p]
  go (NatM x z s) = HVM.Mat (HVM.MAT 0) (termToHVM ctx x) [] [("#Z", [], termToHVM ctx z), ("#S", [], termToHVM ctx s)]
  go (Lst t)      = HVM.Era
  go Nil          = HVM.Ctr "#Nil" []
  go (Con h t)    = HVM.Ctr "#Cons" [termToHVM ctx h, termToHVM ctx t]
  go (LstM x n c) = HVM.Mat (HVM.MAT 0) (termToHVM ctx x) [] [("#Nil", [], termToHVM ctx n), ("#Cons", [], termToHVM ctx c)]
  go (Enu s)      = HVM.Era
  go (Sym s)      = error "TODO: bare Sym toHVM"
  go (EnuM x c e) = error "TODO: bare EnuM toHVM"
  go (Num _)      = HVM.Era
  go (Val (U64_V v)) = HVM.U32 (fromIntegral v)
  go (Val (I64_V v)) = HVM.Era
  go (Val (F64_V v)) = HVM.Era
  go (Val (CHR_V c)) = HVM.Chr c
  go (Op2 o a b)  = op2ToHVM o a b where
    op2ToHVM ADD a b = HVM.Op2 HVM.OP_ADD (termToHVM ctx a) (termToHVM ctx b)
    op2ToHVM SUB a b = HVM.Op2 HVM.OP_SUB (termToHVM ctx a) (termToHVM ctx b)
    op2ToHVM MUL a b = HVM.Op2 HVM.OP_MUL (termToHVM ctx a) (termToHVM ctx b)
    op2ToHVM DIV a b = HVM.Op2 HVM.OP_DIV (termToHVM ctx a) (termToHVM ctx b)
    op2ToHVM MOD a b = HVM.Op2 HVM.OP_MOD (termToHVM ctx a) (termToHVM ctx b)
    op2ToHVM POW a b = error "TODO"
    op2ToHVM EQL a b = HVM.Op2 HVM.OP_EQ  (termToHVM ctx a) (termToHVM ctx b)
    op2ToHVM NEQ a b = HVM.Op2 HVM.OP_NE  (termToHVM ctx a) (termToHVM ctx b)
    op2ToHVM LST a b = HVM.Op2 HVM.OP_LT  (termToHVM ctx a) (termToHVM ctx b)
    op2ToHVM GRT a b = HVM.Op2 HVM.OP_GT  (termToHVM ctx a) (termToHVM ctx b)
    op2ToHVM LEQ a b = HVM.Op2 HVM.OP_LTE (termToHVM ctx a) (termToHVM ctx b)
    op2ToHVM GEQ a b = HVM.Op2 HVM.OP_GTE (termToHVM ctx a) (termToHVM ctx b)
    op2ToHVM AND a b = HVM.Op2 HVM.OP_AND (termToHVM ctx a) (termToHVM ctx b)
    op2ToHVM OR  a b = HVM.Op2 HVM.OP_OR  (termToHVM ctx a) (termToHVM ctx b)
    op2ToHVM XOR a b = HVM.Op2 HVM.OP_XOR (termToHVM ctx a) (termToHVM ctx b)
    op2ToHVM SHL a b = HVM.Op2 HVM.OP_LSH (termToHVM ctx a) (termToHVM ctx b)
    op2ToHVM SHR a b = HVM.Op2 HVM.OP_RSH (termToHVM ctx a) (termToHVM ctx b)
  go (Op1 o a)    = op1ToHVM o a where
    op1ToHVM NOT = error "TODO"
    op1ToHVM NEG = error "TODO"
  go (Sig _ _)    = HVM.Era
  go (Tup x y) = case extractCtr x y of
      Just (k, x) -> HVM.Ctr k (map (termToHVM ctx) x)
      Nothing     -> HVM.Ctr "#P" [termToHVM ctx x, termToHVM ctx y]
    where 
      extractCtr (Sym k) y = 
        case unsnoc (flattenTup y) of
          Just (xs, One) -> Just (k, xs)
          _              -> Nothing
      extractCtr _ _ = Nothing
  go (SigM x f)  = case extractCtrM f of
      Just (cs,(dk,df)) -> HVM.Let HVM.LAZY dk (termToHVM ctx x) (matToHVM ctx dk cs df) -- TODO: Default case should rewrite (ctrNam, ctrBod) to the default case var
      Nothing           -> HVM.Mat (HVM.MAT 0) (termToHVM ctx x) [] [("#P", [], termToHVM ctx f)]
    where
      extractCtrM :: Term -> Maybe ([(String, ([String], Term))], (String, Term))
      extractCtrM (Lam a (subst a -> Lam b (subst b -> EnuM (Var y _) cs (Lam dk (subst dk -> dv))))) =
        if a == y
          then Just ((map (\(k,f) -> (k, flattenCtrM f [])) cs), (dk, dv))
          else Nothing
      extractCtrM _ = Nothing

      flattenCtrM :: Term -> [String] -> ([String], Term)
      flattenCtrM (SigM _ (Lam a (subst a -> Lam b (subst b -> x)))) vars = flattenCtrM x (a : vars)
      flattenCtrM (UniM _ f)                                         vars = (vars, f)
      flattenCtrM _ _ = error "flattenCtrM: unreachable"

      matToHVM :: MS.Map String String -> String -> [(String, ([String], Term))] -> Term -> HVM.Core
      matToHVM ctx x [(ctr,(fds,bod))]    d = HVM.Mat (HVM.IFL 0) (HVM.Var x) [] [(ctr, [], foldr HVM.Lam (termToHVM ctx bod) fds), ("_", [], HVM.Lam x (termToHVM ctx d))]
      matToHVM ctx x ((ctr,(fds,bod)):cs) d = HVM.Mat (HVM.IFL 0) (HVM.Var x) [] [(ctr, [], foldr HVM.Lam (termToHVM ctx bod) fds), ("_", [], HVM.Lam x (matToHVM ctx x cs d))]
      matToHVM _ _ _ _ = error "matToHVM: unreachable"
  go (All _ _)    = HVM.Era
  go (Lam n f)    = HVM.Lam ('&':n) (termToHVM (MS.insert n n ctx) (f (Var n 0)))
  go (App f x)    = HVM.App (termToHVM ctx f) (termToHVM ctx x)
  go (Eql _ _ _)  = HVM.Era
  go Rfl          = HVM.Era
  go (EqlM x f)   = termToHVM ctx f
  go (Met n t ts) = HVM.Era -- TODO: Met
  go (Ind t)      = termToHVM ctx t
  go (Frz t)      = termToHVM ctx t
  go Era          = HVM.Era
  go (Sup l a b)  = HVM.Ref "SUP" 0 [termToHVM ctx l, termToHVM ctx a, termToHVM ctx b]
  go (Frk l a b)  = tmLab where
    -- Only fork variables free in the bodies of a and b
    tmLab             = HVM.Let HVM.STRI "&_L" (termToHVM ctx l) tmDup 
    tmDup             = foldr dup tmSup vars
    tmSup             = HVM.Ref "SUP" 0 [HVM.Var "_L", termToHVM ctxA a, termToHVM ctxB b]
    dup (_,v,(a,b)) x = HVM.Ref "DUP" 0 [HVM.Var "_L", HVM.Var v, HVM.Lam ('&':a) (HVM.Lam ('&':b) x)]
    vars              = [(k, v, (suff v "0", suff v "1")) | (k, v) <- MS.toList ctx]
    suff v s          = if "$$" `isInfixOf` v then v ++ s else v ++ "$$" ++ s
    ctxA              = MS.fromList [(k, a) | (k, _, (a, _)) <- vars]
    ctxB              = MS.fromList [(k, b) | (k, _, (_, b)) <- vars]
  go (Loc s t)    = termToHVM ctx t
  go (Rwt _ _ x)  = termToHVM ctx x
  go (Pri p)      = HVM.Era
  go (Pat x m c)  = HVM.Era

typeToHVM :: Term -> HVM.Core
typeToHVM tm = case tm of
  _ -> error "TODO: typeToHVM"