{-# LANGUAGE MultilineStrings #-}

import Test

-- bug description:
-- see https://github.com/HigherOrderCO/Bend2/issues/18
--
-- Should be inferrable, adding m : Nat annotation does not fix.
-- # ✗ proj
-- # CantInfer:
-- # Context:
-- # - p : Σa:Nat. Nat
-- # Location: (line 8, column 7)
-- # 8 |   m = ~p{(,):λx.λy.x}

cant_infer_pair_proj_assign :: String
cant_infer_pair_proj_assign = """
def proj(p:Σa:Nat.Nat) -> Nat:
  m = ~p{(,):λx.λy.x}
  ()
"""

main :: IO ()
main = testFileChecks cant_infer_pair_proj_assign
