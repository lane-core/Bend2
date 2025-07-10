# FIXME

###

# it would be nice to have a `rewrite` in reverse command, that given A{a==b} substitutes b, instead of a.
# this it would make proofs like the ones of algebra much easier to read and write.
# in such settings we often need to use substituion in reverse,
# and we would like to avoid proving the inverse every time since they are always true
#
# for instance, suppose we want to prove that for nats (that may happen in subproofs for example)
# 
# a+(b+c) = b+(a+c)
#
# then, look at the end to see how this proof works. we need first a
# a small prelude so we can use commutativity and associativity:

# prelude (this can be ignored):
def add_suc_right(a:Nat, b:Nat) -> Nat{add(a, 1n+b) == 1n + add(a,b)}:
  match a:
    case 0n: finally
    case 1n+pa: ind = add_suc_right(pa, b) rewrite ind finally
def unit_right(a:Nat) -> Nat{add(a, 0n) == a}:
  match a:
    case 0n: finally
    case 1n + ap: ind = unit_right(ap) rewrite ind finally
def add(a: Nat, b: Nat) -> Nat:
  match a:
    case 0n: b
    case 1n + p: 1n + add(p, b)
def succ_eq(a:Nat, b:Nat, eq:Nat{a==b}) -> Nat{1n+a==1n+b}:
  match a:
    case 0n: match b:
              case 0n: finally
              case 1n+pb: ~eq {}
    case 1n+pa: match b:
                  case 0n: ~eq {}
                  case 1n+pb: rewrite eq finally
def comm(a:Nat, b:Nat) -> Nat{add(a,b) == add(b,a)}:
  match a:
    case 0n: rewrite unit_right(b) finally
    case 1n + pa: ind = comm(pa,b) rewrite ind rewrite add_suc_right(b,pa) finally
def assoc(a:Nat, b:Nat, c:Nat) -> Nat{add(a,add(b,c)) == add(add(a,b),c)}:
  match a:
    case 0n: finally
    case 1n+pa: ind = assoc(pa,b,c) succ_eq(add(pa,add(b,c)), add(add(pa,b),c), ind)

#
# now the issue. the last line could be much simpler, and this is general:
#

def sym(A:Set, a:A, b:A, eq: A{a==b}) -> A{b==a}:
  rewrite eq finally
def thm(a:Nat, b:Nat, c:Nat) -> Nat{add(a,add(b,c)) == add(b,add(a,c))}:
  rewrite assoc(a,b,c)
  rewrite comm(a,b)
  rewrite sym(Nat, add(b,add(a,c)), add(add(b,a),c), assoc(b,a,c))
  finally

# the line

  # rewrite sym(Nat, add(b,add(a,c)), add(add(b,a),c), assoc(b,a,c))

# could be just
  # rewrite_inv assoc(b,a,c)
