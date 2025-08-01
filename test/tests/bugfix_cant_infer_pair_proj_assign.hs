{-# LANGUAGE MultilineStrings #-}

import Test

-- fixed: f10831ebfc0c709b05a038149f7067b562f10f36
-- It was not being inferred because the eta expansion was not fixing the match on p to be on the canonical form.

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
  0n
"""

main :: IO ()
main = testFileChecks cant_infer_pair_proj_assign
