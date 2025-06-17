def add(a: Nat, b: Nat) -> Nat:
  match a:
    case 0:
      b
    case 1 + aP:
      1 + add(aP, b)

def cong
  ( A: Set
  , B: Set
  , a: A
  , b: A
  , f: A -> B
  , e: A{a == b}
  ) -> B{f(a) == f(b)}:
  match e:
    case {==}:
      {==}

def add_assoc_theo(A: Nat, B: Nat, C: Nat) -> Nat{(add (add A B) C) == (add A (add B C))}:
  match A:
    case 0:
      {==}  # Left:  (0 + B) + C == B + C
           # Right: 0 + (B + C) == B + C
    case 1 + K:
      ind = add_assoc_theo(K, B, C)  # (K + B) + C == K + (B + C)
      cong(Nat, Nat, add(add(K, B), C), add(K, add(B, C)), λx. 1 + x, ind)

add_assoc_theo(1, 2, 3)

