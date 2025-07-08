{-./../Core/Type.hs-}

{-# LANGUAGE ViewPatterns #-}

module Target.HVM where

import Control.Monad (forM)
import Core.Type
import Data.Either (partitionEithers)
import Data.List (isInfixOf, unsnoc)
import Data.Maybe (fromJust, fromMaybe)
import Debug.Trace
import qualified Data.Map as M
import qualified Data.Map.Strict as MS
import qualified Data.Set as S
import qualified HVM.Type as HVM

compile :: Book -> String
compile book@(Book defs) =
  let ds       = map (compileDef book) (M.toList defs)
      (ts, fs) = partitionEithers ds
      main     = "@main = " ++ showHVM (termToHVM book MS.empty (Ref "main")) ++ "\n"
  in prelude ++ main ++ unlines ts ++ unlines fs

prelude :: String
prelude = unlines [
    "// Prelude",
    "data List { #Nil #Cons{head tail} }",
    "data Nat { #Z #S{n} }",
    "data Pair { #P{fst snd} }",
    "@fix(&f) = (f @fix(f))",
    "",
    "// Bend to HVM Compiler Output"
  ]

-- Compile a Bend function to an HVM definition
compileDef :: Book -> (Name, Defn) -> Either String String
compileDef book (nam, (_, tm, ty)) = case extractTypeDef tm of
  Just (_, ctrs) -> Left (compileType nam ctrs ++ "\n" ++ compileFn book nam tm ty)
  Nothing        -> Right (compileFn book nam tm ty)

compileType :: Name -> [(Name, [Name])] -> String
compileType nam ctrs =
  "data " ++ (hvmNam nam) ++ " { " ++ unwords (map compileCtr ctrs) ++ " }"
  where
    compileCtr (nam, fds) = "#" ++ (hvmNam nam) ++ "{" ++ unwords fds ++ "}"

compileFn :: Book -> Name -> Term -> Term -> String
compileFn book nam tm ty =
  "@" ++ (hvmNam nam) ++ "(" ++ unwords (argsStri args body) ++ ") = " ++ showHVM (termToHVM book MS.empty body)
  where
    (args, body) = collectLamArgs tm ty []
    argsStri args bod = map (\k -> if (Just k) == fstMat bod then "!&"++k else "&"++k) args
    fstMat bod  = case cut bod of
      BitM (cut -> Var k _) _ _ -> Just k
      NatM (cut -> Var k _) _ _ -> Just k
      LstM (cut -> Var k _) _ _ -> Just k
      SigM (cut -> Var k _) _   -> Just k
      Let _ (Lam k (subst k -> f)) -> fstMat f
      SupM _ _ (Lam a (subst a -> Lam b (subst b -> f))) -> fstMat f
      _ -> Nothing

-- Extract constructor definition info from type definitions
extractTypeDef :: Term -> Maybe ([Name], [(Name, [Name])])
extractTypeDef tm = do
  (args, tmSig) <- getTypeArgs tm []
  css <- getTypeCss tmSig
  return (args, css)
  where
    getTypeArgs :: Term -> [Name] -> Maybe ([Name], Term)
    getTypeArgs (Lam arg tm) args = getTypeArgs (tm (Var arg 0)) (args ++ [arg])
    getTypeArgs tm           args = Just (args, tm)

    getTypeCss :: Term -> Maybe [(Name, [Name])]
    getTypeCss (Sig (Enu _) (Lam "ctr" (subst "ctr" -> EnuM (Var "ctr" _) css (Lam "_" (subst "_" -> One))))) = do
      forM css (\(ctr, bod) -> do
        fds <- getTypeCsFds bod
        return (ctr, fds))
    getTypeCss _ = Nothing

    getTypeCsFds :: Term -> Maybe [Name]
    getTypeCsFds (Sig _ (Lam fd (subst fd -> tm))) = do
      fds <- getTypeCsFds tm
      return $ fd : fds
    getTypeCsFds Uni = Just []
    getTypeCsFds _   = Nothing

termToHVM :: Book -> MS.Map Name HVM.Name -> Term -> HVM.Core
termToHVM book ctx term = go term where
  go (Var n i) =
    case MS.lookup n ctx of
      Just n  -> HVM.Var n
      Nothing -> HVM.Var n
  go (Ref k)      = fromJust (refAppToHVM book ctx term)
  go (Sub t)      = termToHVM book ctx t
  go (Fix n f)    = HVM.Ref "fix" 0 [HVM.Lam ('&':n) (termToHVM book (MS.insert n n ctx) (f (Var n 0)))]
  go (Let v f)    =
    case f of
      (Lam n (subst n -> f)) -> HVM.Let HVM.LAZY n (termToHVM book ctx v) (termToHVM book ctx f)
      _                      -> HVM.App (termToHVM book ctx f) (termToHVM book ctx v)
  go Set          = HVM.Era
  go (Chk v t)    = termToHVM book ctx v
  go Emp          = HVM.Era
  go (EmpM x)     = HVM.Era
  go Uni          = HVM.Era
  go One          = HVM.U32 1
  go (UniM x f)   = termToHVM book ctx f
  go Bit          = HVM.Era
  go Bt0          = HVM.U32 0
  go Bt1          = HVM.U32 1
  go (BitM x f t) = HVM.Mat HVM.SWI (termToHVM book ctx x) [] [("0", [], termToHVM book ctx f), ("_", [], termToHVM book ctx t)]
  go Nat          = HVM.Era
  go Zer          = HVM.Ctr "#Z" []
  go (Suc p)      = HVM.Ctr "#S" [termToHVM book ctx p]
  go (NatM x z s) =
    case s of
      (Lam n (subst n -> s)) ->
        HVM.Mat (HVM.MAT 0) (termToHVM book ctx x) [] [("#Z", [], termToHVM book ctx z), ("#S", [n], termToHVM book ctx s)]
      _ ->
        HVM.Mat (HVM.MAT 0) (termToHVM book ctx x) [] [("#Z", [], termToHVM book ctx z), ("#S", ["x$p"], HVM.App (termToHVM book ctx s) (HVM.Var "x$p"))]
  go (Lst t)      = HVM.Era
  go Nil          = HVM.Ctr "#Nil" []
  go (Con h t)    = HVM.Ctr "#Cons" [termToHVM book ctx h, termToHVM book ctx t]
  go (LstM x n c) =
    case c of
      (Lam h (subst h -> (Lam t (subst t -> c)))) ->
        HVM.Mat (HVM.MAT 0) (termToHVM book ctx x) [] [("#Nil", [], termToHVM book ctx n), ("#Cons", [h, t], termToHVM book ctx c)]
      _ ->
        HVM.Mat (HVM.MAT 0) (termToHVM book ctx x) [] [("#Nil", [], termToHVM book ctx n), ("#Cons", ["x$h", "x$t"], HVM.App (HVM.App (termToHVM book ctx c) (HVM.Var "x$h")) (HVM.Var "x$t"))]
  go (Enu s)      = HVM.Era
  go (Sym s)      = error "TODO: bare Sym toHVM"
  go (EnuM x c e) = error "TODO: bare EnuM toHVM"
  go (Log s x)    = termToHVM book ctx x  -- For HVM, just return the result expression
  go (Num _)      = HVM.Era
  go (Val v)      = valToHVM book ctx v
  go (Op2 o a b)  = op2ToHVM book ctx o a b
  go (Op1 o a)    = op1ToHVM book ctx o a
  go (Sig _ _)    = HVM.Era
  go (Tup x y)    =
    case ctrToHVM book ctx x y of
      Just hvm -> hvm
      Nothing -> HVM.Ctr "#P" [termToHVM book ctx x, termToHVM book ctx y]
  go (SigM x f)   =
    case ctrMToHVM book ctx x f of
      Just hvm -> hvm
      Nothing -> case f of
        (Lam l (subst l -> (Lam r (subst r -> f)))) ->
          HVM.Mat (HVM.MAT 0) (termToHVM book ctx x) [] [("#P", [l, r], termToHVM book ctx f)]
        _ ->
          HVM.Mat (HVM.MAT 0) (termToHVM book ctx x) [] [("#P", ["x$l", "x$r"], HVM.App (HVM.App (termToHVM book ctx f) (HVM.Var "x$l")) (HVM.Var "x$r"))]
  go (All _ _)    = HVM.Era
  go (Lam n f)    = HVM.Lam ('&':n) (termToHVM book (MS.insert n n ctx) (f (Var n 0)))
  go (App f x)    =
    case refAppToHVM book ctx term of
      Just hvm -> hvm
      Nothing -> HVM.App (termToHVM book ctx f) (termToHVM book ctx x)
  go (Eql _ _ _)  = HVM.Era
  go Rfl          = HVM.Era
  go (EqlM x f)   = termToHVM book ctx f
  go (Met n t ts) = HVM.Era -- TODO: Met
  go (Ind t)      = termToHVM book ctx t
  go (Frz t)      = termToHVM book ctx t
  go Era          = HVM.Era
  go (Sup l a b)  = HVM.Ref "SUP" 0 [termToHVM book ctx l, termToHVM book ctx a, termToHVM book ctx b]
  go (SupM x l f) = HVM.Ref "DUP" 0 [termToHVM book ctx l, termToHVM book ctx x, termToHVM book ctx f]
  go (Frk l a b)  = HVM.Era
  go (Loc s t)    = termToHVM book ctx t
  go (Rwt _ _ x)  = termToHVM book ctx x
  go (Pri p)      = HVM.Era
  go (Pat x m c)  = HVM.Era

ctrToHVM :: Book -> MS.Map Name HVM.Name -> Term -> Term -> Maybe HVM.Core
ctrToHVM book ctx x y = case (x, (unsnoc (flattenTup y))) of
  (Sym k, Just (xs, One)) -> Just (HVM.Ctr ('#':hvmNam k) (map (termToHVM book ctx) xs))
  _ -> Nothing

ctrMToHVM :: Book -> MS.Map Name HVM.Name -> Term -> Term -> Maybe HVM.Core
ctrMToHVM book ctx x f = case f of
  (Lam k0 (subst k0 -> Lam kb (subst kb -> EnuM (Var k2 _) cs (Lam kt (subst kt -> d))))) ->
    if k0 == k2 then do
      cs <- forM cs (\(ctr, f) -> do
          (fds, bod) <- flattenCase kb f []
          return (ctr, fds, bod)
        )
      case d of
        -- TODO: Should look at type instead of looking for One, will bug if default should actually return One.
        (Lam k (subst k -> One)) -> return $ mkMat x cs
        _                        -> return $ (mkIfl x kt kb cs d)
    else Nothing
  _ -> Nothing
  where
    -- Flatten the matches that form a ctr match case into (fds, bod)
    flattenCase :: Name -> Term -> [Name] -> Maybe ([Name], Term)
    flattenCase k0 f fds = case f of
      (SigM (Var k1 _) (Lam fd (subst fd -> Lam k2 (subst k2 -> f)))) -> if (k0 == k1) then flattenCase k2 f (fds++[fd]) else Nothing
      (UniM (Var k1 _) f)                                             -> if (k0 == k1) then Just (fds, f) else Nothing
      _ -> Nothing

    mkMat :: Term -> [(Name, [Name], Term)] -> HVM.Core
    mkMat x cs =
      HVM.Mat (HVM.MAT 0) (termToHVM book ctx x) [] csToHVM
      where csToHVM = map (\(ctr,fds,bod) -> ('#':hvmNam ctr, (map ('&':) fds), termToHVM book ctx bod)) cs

    mkIfl :: Term -> Name -> Name -> [(Name, [Name], Term)] -> Term -> HVM.Core
    mkIfl x kt kb [(ctr,fds,bod)]    d = mkIflCase x kt ctr (termToHVM book ctx bod) fds d2
                            -- Converted EnuM + SigM to single Mat, rewrite (kt,kb) to just kt since we now use only 1 var.
                            where d2 = (rewriteHVM (HVM.Ctr "#P" [HVM.Var kt, HVM.Var kb]) (HVM.Var kt) (termToHVM book ctx d))
    mkIfl x kt kb ((ctr,fds,bod):cs) d = mkIflCase x kt ctr (termToHVM book ctx bod) fds (mkIfl (Var kt 0) kt kb cs d)
    mkIfl _ _ _ _ _ = error "mkIfl: unreachable"

    mkIflCase x kt ctr bod fds d = 
      HVM.Mat (HVM.IFL 0) (termToHVM book ctx x) [] [
          ('#':hvmNam ctr, (map ('&':) fds), bod),
          (('&':kt), [], d)
        ]

valToHVM :: Book -> MS.Map Name HVM.Name -> NVal -> HVM.Core
valToHVM book ctx (U64_V v) = HVM.U32 (fromIntegral v)
valToHVM book ctx (I64_V v) = HVM.Era
valToHVM book ctx (F64_V v) = HVM.Era
valToHVM book ctx (CHR_V c) = HVM.Chr c

op2ToHVM :: Book -> MS.Map Name HVM.Name -> NOp2 -> Term -> Term -> HVM.Core
op2ToHVM book ctx ADD a b = HVM.Op2 HVM.OP_ADD (termToHVM book ctx a) (termToHVM book ctx b)
op2ToHVM book ctx SUB a b = HVM.Op2 HVM.OP_SUB (termToHVM book ctx a) (termToHVM book ctx b)
op2ToHVM book ctx MUL a b = HVM.Op2 HVM.OP_MUL (termToHVM book ctx a) (termToHVM book ctx b)
op2ToHVM book ctx DIV a b = HVM.Op2 HVM.OP_DIV (termToHVM book ctx a) (termToHVM book ctx b)
op2ToHVM book ctx MOD a b = HVM.Op2 HVM.OP_MOD (termToHVM book ctx a) (termToHVM book ctx b)
op2ToHVM book ctx POW a b = error "TODO"
op2ToHVM book ctx EQL a b = HVM.Op2 HVM.OP_EQ  (termToHVM book ctx a) (termToHVM book ctx b)
op2ToHVM book ctx NEQ a b = HVM.Op2 HVM.OP_NE  (termToHVM book ctx a) (termToHVM book ctx b)
op2ToHVM book ctx LST a b = HVM.Op2 HVM.OP_LT  (termToHVM book ctx a) (termToHVM book ctx b)
op2ToHVM book ctx GRT a b = HVM.Op2 HVM.OP_GT  (termToHVM book ctx a) (termToHVM book ctx b)
op2ToHVM book ctx LEQ a b = HVM.Op2 HVM.OP_LTE (termToHVM book ctx a) (termToHVM book ctx b)
op2ToHVM book ctx GEQ a b = HVM.Op2 HVM.OP_GTE (termToHVM book ctx a) (termToHVM book ctx b)
op2ToHVM book ctx AND a b = HVM.Op2 HVM.OP_AND (termToHVM book ctx a) (termToHVM book ctx b)
op2ToHVM book ctx OR  a b = HVM.Op2 HVM.OP_OR  (termToHVM book ctx a) (termToHVM book ctx b)
op2ToHVM book ctx XOR a b = HVM.Op2 HVM.OP_XOR (termToHVM book ctx a) (termToHVM book ctx b)
op2ToHVM book ctx SHL a b = HVM.Op2 HVM.OP_LSH (termToHVM book ctx a) (termToHVM book ctx b)
op2ToHVM book ctx SHR a b = HVM.Op2 HVM.OP_RSH (termToHVM book ctx a) (termToHVM book ctx b)

op1ToHVM :: Book -> MS.Map Name HVM.Name -> NOp1 -> Term -> HVM.Core
op1ToHVM book ctx NOT = error "TODO"
op1ToHVM book ctx NEG = error "TODO"

refAppToHVM :: Book -> MS.Map Name HVM.Name -> Term -> Maybe HVM.Core
refAppToHVM book ctx term =
  case collectApps term [] of
    (Ref k, args) ->
      let (_,tm,ty) = fromJust (deref book k)
          args'    = map (termToHVM book ctx) args
          len      = length args
          ari      = length (fst (collectLamArgs tm ty []))
      in wrapRef ctx k args' len ari
    _ -> Nothing
  where
    wrapRef ctx k args len ari
      | len <  ari = do
        let var = "_a" ++ show len
        bod <- wrapRef (MS.insert var var ctx) k (args ++ [HVM.Var var]) (len+1) ari
        return $ HVM.Lam ('&':var) bod
      | len == ari = do
        return $ HVM.Ref (hvmNam k) 0 args
      | len >  ari = do
        let (refArgs, appArgs) = splitAt ari args
        let call = HVM.Ref (hvmNam k) 0 refArgs
        return $ foldl HVM.App call appArgs
      | otherwise = undefined

-- Utils
--------

hvmNam :: Name -> HVM.Name
hvmNam n = (replace '/' "__" n) ++ "$"

subst :: Name -> Body -> Term
subst a f = f (Var a 0)

replace :: Char -> String -> String -> String
replace old new xs = foldr (\c acc -> if c == old then new ++ acc else c : acc) [] xs

collectLamArgs :: Term -> Term -> [Name] -> ([Name], Term)
collectLamArgs (Lam arg (subst arg -> bod)) (All _ (Lam x (subst x -> ty))) args = collectLamArgs bod ty (args ++ [arg])
collectLamArgs bod ty args = (args, bod)

-- Rewrite structurally identical HVM terms
rewriteHVM :: HVM.Core -> HVM.Core -> HVM.Core -> HVM.Core
rewriteHVM old new tm =
  if tm == old
    then new
    else case tm of
      HVM.Var n         -> HVM.Var n
      HVM.Ref n k xs    -> HVM.Ref n k (map (rewriteHVM old new) xs)
      HVM.Era           -> HVM.Era
      HVM.Lam n f       -> HVM.Lam n (rewriteHVM old new f)
      HVM.App f x       -> HVM.App (rewriteHVM old new f) (rewriteHVM old new x)
      HVM.Sup l a b     -> HVM.Sup l (rewriteHVM old new a) (rewriteHVM old new b)
      HVM.Dup l a b v x -> HVM.Dup l a b (rewriteHVM old new v) (rewriteHVM old new x)
      HVM.Ctr n xs      -> HVM.Ctr n (map (rewriteHVM old new) xs)
      HVM.U32 n         -> HVM.U32 n
      HVM.Chr c         -> HVM.Chr c
      HVM.Op2 o a b     -> HVM.Op2 o (rewriteHVM old new a) (rewriteHVM old new b)
      HVM.Let t n v f   -> HVM.Let t n (rewriteHVM old new v) (rewriteHVM old new f)
      HVM.Mat t x mv cs -> HVM.Mat t (rewriteHVM old new x) (map (\(n,v) -> (n,rewriteHVM old new v)) mv) (map (\(c,f,b) -> (c,f,rewriteHVM old new b)) cs)
      HVM.Inc a         -> HVM.Inc (rewriteHVM old new a)
      HVM.Dec a         -> HVM.Dec (rewriteHVM old new a)

-- Alternative HVM show function suitable for compiler output
showHVM :: HVM.Core -> String
showHVM (HVM.Var k)         = k
showHVM (HVM.Ref k i xs)    = "@" ++ k ++ "(" ++ unwords (map showHVM xs) ++ ")"
showHVM HVM.Era             = "*"
showHVM (HVM.Lam x f)       = "λ" ++ x ++ " " ++ showHVM f
showHVM (HVM.App f x)       = "(" ++ showHVM f ++ " " ++ showHVM x ++ ")"
showHVM (HVM.Sup l a b)     = "&" ++ show l ++ "{" ++ showHVM a ++ " " ++ showHVM b ++ "}"
showHVM (HVM.Dup l x y v f) = "! &" ++ show l ++ "{" ++ x ++ " " ++ y ++ "} = " ++ showHVM v ++ "\n" ++ showHVM f
showHVM (HVM.Ctr k xs)      = k ++ "{" ++ unwords (map showHVM xs) ++ "}"
showHVM (HVM.U32 v)         = show v
showHVM (HVM.Chr v)         = "'" ++ [v] ++ "'"
showHVM (HVM.Op2 o a b)     = "(" ++ show o ++ " " ++ showHVM a ++ " " ++ showHVM b ++ ")"
showHVM (HVM.Let m k v f)   = "! " ++ show m ++ k ++ " = " ++ showHVM v ++ "; " ++ showHVM f
showHVM (HVM.Mat k v m ks)  = "~ " ++ showHVM v ++ " " ++ concatMap showMov m ++ " {" ++ unwords (map showCase ks) ++ "}"
    where showMov (k,v)     = " !" ++ k ++ "=" ++ showHVM v
          showCase (c,[],b) = c ++ ": " ++ showHVM b
          showCase (c, f,b) = c ++ "{" ++ unwords f ++ "}" ++ ": " ++ showHVM b
showHVM (HVM.Inc x)         = "↑" ++ showHVM x
showHVM (HVM.Dec x)         = "↓" ++ showHVM x
