# FIXME

# of course - you don't need absurdity, just:
# def main() -> Empty: main()
# suffices to prove False, obviously - without a termination checker, a proof
# assistant with unrestricted recursion is necessarily inconsistent. this will
# only be fixed when the termination checker is added

###

# while we don't have a termination checker we can prove absurdity in bend
# this checks, although it never halts

  # ✓ absurdity
  # ✓ main


def absurdity(A: Set) -> A:
  absurdity(A)

def main() -> Empty:
  absurdity(Empty)

