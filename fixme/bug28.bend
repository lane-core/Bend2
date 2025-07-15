# FIXME

###

# incorrect annotation of variable causes it to check (compare to bug27)

def proj(p:Σa:Nat.Nat) -> Nat:
  (m :: Bool) = ~p{(,):λx.λy.x}
  m

def main() -> Nat:
  proj((2n,10n))

  # ✓ main
  # ✓ proj
  #
  # 1n+1n+0n
