{-# LANGUAGE MultilineStrings #-}

-- bug description:
-- see https://github.com/HigherOrderCO/Bend2/issues/20
--
-- Incorrect annotation does not stop it from type checking.
import Test

incorrect_ann_checks :: String
incorrect_ann_checks = """
def proj(p:Σa:Nat.Nat) -> Nat:
  (m :: Bool) : Nat = ~p{(,):λx.λy.x}
  m

def main() -> Nat:
  proj((2n,10n))
"""

main :: IO ()
main = testFile incorrect_ann_checks
  "incorrect annotation should not type check" $ \out err -> do
    assert (err `has` "Mismatch:")
