# FIXME

###

# while we don't have a termination checker we can prove absurdity in bend
# this checks, although it never halts

  # ✓ absurdity
  # ✓ main


def absurdity(A: Set) -> A:
  absurdity(A)

def main() -> Empty:
  absurdity(Empty)

