namespace SortingAlgorithms


----------------------------------------------------------------------------------------------------
-- Insert sort implementation
----------------------------------------------------------------------------------------------------


def insert (x : Nat) : List Nat → List Nat
  | []      => [x]
  | y :: ys =>
      if x ≤ y then x :: y :: ys
      else y :: insert x ys

def insertSort : List Nat → List Nat
  | []      => []
  | x :: xs => insert x (insertSort xs)


----------------------------------------------------------------------------------------------------
-- Concrete Examples
----------------------------------------------------------------------------------------------------


#eval insert 5 []
-- Output: [5]

#eval insert 1 [2, 3, 4]
-- Output: [1, 2, 3, 4]

#eval insert 3 [1, 2, 4, 5]
-- Output: [1, 2, 3, 4, 5]

#eval insert 6 [1, 2, 3]
-- Output: [1, 2, 3, 6]

#eval insert 3 [1, 3, 5]
-- Output: [1, 3, 3, 5]


----------------------------------------------------------------------------------------------------
-- Formal Verification
----------------------------------------------------------------------------------------------------


open List -- for the `~` notation which expresses one list being a permutation of another

theorem insert_perm (x : Nat) (l : List Nat) : insert x l ~ x :: l := by sorry

theorem insertSort_perm (l : List Nat) : insertSort l ~ l := by sorry

theorem insert_length (x : Nat) (l : List Nat) : (insert x l).length = l.length + 1 := by sorry


def IsSortedPairwise (l : List Nat) : Prop := List.Pairwise (· ≤ ·) l

theorem insertSort_sorted (l : List Nat) : IsSortedPairwise (insertSort l) := by sorry


end SortingAlgorithms
