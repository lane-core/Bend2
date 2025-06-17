def con(s: Nat, xs: Bit[s][], ys:Bit[s][]) -> Bit[s][]:
  match xs:
    case []:
      ys
    case x<>xs:
      x <> con(s, xs, ys)

def map(s: Nat, b: Bit, xs: Bit[s][]) -> Bit[1+s][]:
  match xs:
    case []:
      []
    case x<>xs:
      (b <> x) <> map(s, b, xs)


def n0() -> Bit[3]:
  [#0, #0, #0]
def n1() -> Bit[3]:
  [#0, #0, #1]
def n2() -> Bit[3]:
  [#0, #1, #0]
def n3() -> Bit[3]:
  [#0, #1, #1]
def n4() -> Bit[3]:
  [#1, #0, #0]
def n5() -> Bit[3]:
  [#1, #0, #1]
def n6() -> Bit[3]:
  [#1, #1, #0]

gen qsort(s: Nat, xs: Bit[1+s][], min: ∅Bit[s][], max: ∅Bit[s][]) -> Bit[1+s][]
  with con
  with map

let qsort(2, [n3,n1,n2,n0], [], []) == [n0,n1,n2,n3] : Bit[3][]

view(qsort)
