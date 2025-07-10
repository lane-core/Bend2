# FIXME

####

# type inference of variables makes organization difficult:

# one way to prove that a second order And implies a Pair,
# is to write a completely unalised proof such as this:

def thm_ugly(A:Set, B:Set)   -> (∀C:Set. (A->B->C) -> C) -> Σa:A.B:
  λnd. nd(Σa:A.B)(λa1.λb1.(a1,b1))

#which checks
  # ✓ thm_ugly

# if we try to separate this into intermediate terms for organization, it won't work,
# as now with the var in the assignment, outside of its place as an argument, 
# bend won't be able to infer its type:

def thm_pretty(A:Set, B:Set) -> (∀C:Set. (A->B->C) -> C) -> Σa:A.B:
  λnd.
    a_then_b_then_pair = λa1.λb1.(a1,b1)
    nd(Σa:A.B)(λa1.λb1.(a1,b1))

# this gives the error
  # ✗ thm_pretty
  # CantInfer:
  # Context:
  # - A : Set
  # - B : Set
  # - nd : ∀C:Set. (A -> B -> C) -> C
  # Location: (line 16, column 26)
  # 16 |     a_then_b_then_pair = λa1.λb1.(a1,b1)

# the only way to get this organized is to write separate functions, since def is annotated.
# this is not completely following the WanShi 1 function/1 file convention

def thm_pretty_aux(A:Set, B:Set) -> (∀C:Set. (A->B->C) -> C) -> Σa:A.B:
  λnd. nd(Σa:A.B)(aux(A,B))

def aux(A:Set, B:Set, a:A, b:B) -> Σa:A.B:
  (a,b)

# this checks
  # ✓ aux
  # ✓ thm_pretty_aux
