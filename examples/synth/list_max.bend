def max(a: Nat, b: Nat) -> Nat:
  match a:
    case 0:
      b
    case 1+n:
      match b:
        case 0:
          1+n
        case 1+n1:
          1+max(n, n1)

gen list_max(a: ~Nat[]) -> Nat {max}

tst list_max([]) == 0 : Nat
tst list_max([1, 5, 9]) == 9 : Nat
tst list_max([4, 2, 3]) == 4 : Nat
tst list_max([1, 5, 3, 8, 7, 4]) == 8 : Nat
tst list_max([2, 3]) == 3 : Nat

end
()

# λmax.λlist_max.λ{[]:0; h<>t: ((max x) (max_list t))}
# λa.λb.λ{[]:0;<>:λc.λd.((a c) (b d))}

