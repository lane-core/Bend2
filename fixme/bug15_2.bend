# FIXME

###

# a fix to this bug in commit 5020e1b6f13661e504f91cab95d957cdbedfc15b caused bug15

  # ✗ attach_has_left_inv
  # Mismatch:
  # - Goal: ∀a:A. A{g(f(a))==a}
  # - Type: ∀a:A. A{a==a}
  # Context:
  # - A : Set
  # - f : ∀a:A. Σa:A. Unit
  # - g : ∀t:Σa:A. Unit. A
  # Location: (line 35, column 57)
  # 35 |   exists_intro(X -> Y, λh.is_left_inverse<Y,X>(h,f), g, dettach_left_inv_attach<Y>())

# the error disappear if in this last line we change f and g by the right-hand-side of their assignments (their values)

  # change: exists_intro(X -> Y, λh.is_left_inverse<Y,X>(h,        f),          g, dettach_left_inv_attach<Y>())
  #     to: exists_intro(X -> Y, λh.is_left_inverse<Y,X>(h,attach<Y>), dettach<Y>, dettach_left_inv_attach<Y>())

def exists(A : Set, P: A -> Set) -> Set:
  ∀C:Set . ((∀a:A . (P(a) -> C)) -> C)

def exists_intro : ∀A: Set . (∀P: A -> Set . (∀a:A . (∀pa:P(a) . (exists(A,P))))) =
  λA.λP.λa.λpa.λC.λI.I(a)(pa)

def is_left_inverse<A,B>(g: B->A, f:A->B) -> Set:
  ∀a:A . A{g(f(a)) == a}

def has_left_inverse<A,B>(f: A->B) -> Set:
  exists(B->A, λg . is_left_inverse<A,B>(g,f)) 

def dettach<A>(t:Σa:A.Unit) -> A:
  match t:
    case (a,b): a
def attach<A>(a:A) -> Σa:A.Unit:
  (a,())

def dettach_left_inv_attach<A>() -> is_left_inverse<A,Σa:A.Unit>(dettach<A>,attach<A>):
  λa.finally

def attach_has_left_inv<A>() -> has_left_inverse<A,Σa:A.Unit>(attach<A>):
  X = Σa:A.Unit
  Y = A
  f = attach<Y>
  g = dettach<Y>
  exists_intro(X -> Y, λh.is_left_inverse<Y,X>(h,f), g, dettach_left_inv_attach<Y>())
  # exists_intro(X -> Y, λh.is_left_inverse<Y,X>(h,attach<Y>), dettach<Y>, dettach_left_inv_attach<Y>())


