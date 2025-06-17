
def add(n: Nat, y: Nat) -> Nat:
  match n:
    case 0:
      y
    case 1+nP:
      1+add(nP, y)

def mul(n: Nat, y: Nat) -> Nat:
  match n y:
    case 0 0:
      0
    case 0 1+yP:
      0
    case 1+nP 0:
      0
    case 1+nP 1+yP:
      add((1+yP), mul(nP, (1+yP)))

def factorial(n: Nat) -> Nat:
  match n:
    case 0:
      1
    case 1+nP:
      mul(1+nP, factorial(nP)) 

factorial(4)


