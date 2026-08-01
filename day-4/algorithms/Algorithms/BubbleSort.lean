namespace SortingAlgorithms


----------------------------------------------------------------------------------------------------
-- Bubble sort implementation
----------------------------------------------------------------------------------------------------

def bubble : List Nat → List Nat
  | [] => []
  | [x] => [x]
  | x :: y :: tail =>
    if x > y then y :: bubble (x :: tail)
    else x :: bubble (y :: tail)

def bubbleSort : List Nat → Nat → List Nat
  | l, 0 => l
  | l, n + 1 => bubbleSort (bubble l) n


----------------------------------------------------------------------------------------------------
-- Concrete Examples
----------------------------------------------------------------------------------------------------


#eval bubble [4, 3, 5, 1, 2]
-- Output: [3, 4, 1, 2, 5]  (Notice how 5 "bubbled" to the right)

#eval bubble (bubble [4, 3, 5, 1, 2])
-- Output: [3, 1, 2, 4, 5]

#eval bubbleSort [4, 3, 5, 1, 2] 5
-- Output: [1, 2, 3, 4, 5]

#eval bubbleSort [10, 8, 2, 7, 3, 1] 6
-- Output: [1, 2, 3, 7, 8, 10]


----------------------------------------------------------------------------------------------------
-- Formal Verification
----------------------------------------------------------------------------------------------------


open List -- for the `~` notation which expresses one list being a permutation of another

theorem bubble_perm (l : List Nat) : bubble l ~ l := by sorry

theorem bubbleSort_perm (l : List Nat) (n : Nat) : bubbleSort l n ~ l := by sorry

theorem bubble_length (l : List Nat) : (bubble l).length = l.length := by sorry


def IsSortedPairwise (l : List Nat) : Prop := List.Pairwise (· ≤ ·) l

theorem bubbleSort_sorted (l : List Nat) : IsSortedPairwise (bubbleSort l l.length) := by sorry


end SortingAlgorithms
