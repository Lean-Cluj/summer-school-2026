import Mathlib.Order.MinMax


namespace MaxList


----------------------------------------------------------------------------------------------------
-- Maximum element in a list
----------------------------------------------------------------------------------------------------


def maxList : List Nat → Nat
 | [] => 0
 | x :: xs => max x (maxList xs)


----------------------------------------------------------------------------------------------------
-- Concrete Examples
----------------------------------------------------------------------------------------------------


#eval maxList []
-- Output: 0

#eval maxList [7]
-- Output: 7

#eval maxList [4, 12, 3, 8]
-- Output: 12

#eval maxList [42, 17, 5, 1]
-- Output: 42

#eval maxList [1, 5, 9, 20]
-- Output: 20


----------------------------------------------------------------------------------------------------
-- Formal Verification
----------------------------------------------------------------------------------------------------


theorem le_maxList {l : List Nat} {x : Nat} (h : x ∈ l) :
   x ≤ maxList l := by
 induction l with
 | nil => cases h
 | cons y ys ih =>
   cases h with
   | head _ => unfold maxList; exact Nat.le_max_left _ _
   | tail _ h' => unfold maxList; exact Nat.le_trans (ih h') (Nat.le_max_right _ _)

theorem maxList_mem {l : List Nat} (h : l ≠ []) : maxList l ∈ l := by
  induction l with
  | nil => contradiction
  | cons x xs ih =>
    clear h
    cases xs with
    | nil =>
      have h1 : maxList [x] = x := by
        unfold maxList
        exact max_eq_left (Nat.zero_le _)
      rw [h1]
      exact List.Mem.head _
    | cons y ys =>
      have h_max : maxList (x :: y :: ys) = x ∨ maxList (x :: y :: ys) = maxList (y :: ys) := by
        unfold maxList
        exact max_choice x (maxList (y :: ys))
      rcases h_max with h1 | h2
      · rw [h1]
        exact List.Mem.head _
      · rw [h2]
        apply List.Mem.tail
        apply ih
        simp

----------------------------------------------------------------------------------------------------
-- Other implementations
----------------------------------------------------------------------------------------------------


def maxList? : List Nat → Option Nat
 | [] => none
 | x :: xs => some (xs.foldr max x)

def maxList' : List Nat → Nat
 | [] => 0
 | [x] => x
 | x :: y :: ys => max x (maxList' (y :: ys))


end MaxList
