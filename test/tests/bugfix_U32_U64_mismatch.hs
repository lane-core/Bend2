{-# LANGUAGE MultilineStrings #-}

import Test

-- FIXED

-- HVM3 uses U32 numbers while bend2 uses U64 numbers.
-- Values will be silently truncated during compilation and the results of numerical operations will be incorrect.
-- This is a bug.

u32_u64_mismatch :: String
u32_u64_mismatch = """
def main() -> Bool:
  # 1048576 * 1048576 # Should be 1099511627776
  True
  assert (1048576 * 1048576) == 1099511627776 : U64
"""

main :: IO ()
main = testFileChecks u32_u64_mismatch
