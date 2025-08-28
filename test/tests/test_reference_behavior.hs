{-# LANGUAGE MultilineStrings #-}

import Test

-- Test the exact same construct as the reference implementation
reference_mismatch_bend :: String
reference_mismatch_bend = """
def main : Nat = True
"""

main :: IO ()
main = testFile reference_mismatch_bend "test reference Bool/Nat mismatch behavior" $ \out err -> do
  putStrLn $ "DEBUG - out: '" ++ out ++ "'"
  putStrLn $ "DEBUG - err: '" ++ err ++ "'"
  if err `has` "Mismatch:"
    then putStrLn "✅ Type mismatch correctly caught (same as reference)"
    else putStrLn "❌ Type mismatch not caught - behavior differs from reference"