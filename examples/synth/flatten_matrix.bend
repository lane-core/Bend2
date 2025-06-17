gen flatten_matrix(matrix: ~{~{Nat[]}[]}) -> Nat[]

tst flatten_matrix([[1, 2, 3], [4, 5, 6], [7, 8, 9]]) == [1, 2, 3, 4, 5, 6, 7, 8, 9] : Nat[]
tst flatten_matrix([[2, 2], [2, 2]]) == [2, 2, 2, 2] : Nat[]

end
()
