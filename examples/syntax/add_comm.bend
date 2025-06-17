# Natural number addition
def add(a: Nat, b: Nat) -> Nat:
    match a:
        case 0: b
        case 1+aP: ↑add(aP, b)

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

def add_zero_right(A: Nat) -> Nat{add(A, 0) == A}:
  match A:
    case 0: {==}  # add(0, 0) = 0 = 0
    case 1 + K:
      let ind = add_zero_right(K)  # add(K, 0) = K
      cong(Nat, Nat, add(K, 0), K, λx. ↑x, ind)  # 1 + add(K, 0) = 1 + K

def add_succ_right(A: Nat, B: Nat) -> Nat{add(A, 1 + B) == 1 + add(A, B)}:
  match A:
    case 0: {==}  # add(0, 1 + B) = 1 + B = 1 + add(0, B)
    case 1 + K:
      let ind = add_succ_right(K, B)  # add(K, 1 + B) = 1 + add(K, B)
      cong(Nat, Nat, add(K, 1 + B), 1 + add(K, B), λx. ↑x, ind)  # 1 + add(K, 1 + B) = 1 + (1 + add(K, B))

# add_zero_right(2)

def add_comm_theo(A: Nat, B: Nat) -> Nat{add(A, B) == add(B, A)}:
  match A:
    case 0:
      let lemma = add_zero_right(B)  # add(B, 0) = B
      {==}  # add(0, B) = B = add(B, 0)
    case 1 + K:
      let ind = add_comm_theo(K, B)  # add(K, B) = add(B, K)
      let lemma = add_succ_right(B, K)  # add(B, 1 + K) = 1 + add(B, K)
      let step = cong(Nat, Nat, add(K, B), add(B, K), λx. ↑x, ind)  # 1 + add(K, B) = 1 + add(B, K)
      step

()
