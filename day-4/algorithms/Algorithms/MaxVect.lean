import Mathlib.Order.MinMax -- for max_choice
import Mathlib.Data.Vector.Mem


namespace MaxVect


----------------------------------------------------------------------------------------------------
-- Maximum element in a vector
----------------------------------------------------------------------------------------------------


def maxVect : {n : Nat} → List.Vector Nat n → Nat
 | 0,     _ => 0
 | _ + 1, v => max v.head (maxVect v.tail)


----------------------------------------------------------------------------------------------------
-- Concrete Examples
----------------------------------------------------------------------------------------------------


#eval maxVect ⟨[],rfl⟩
-- Output: 0

#eval maxVect ⟨[7],rfl⟩
-- Output: 7

#eval maxVect ⟨[4, 12, 3, 8],rfl⟩
-- Output: 12

#eval maxVect ⟨[42, 17, 5, 1],rfl⟩
-- Output: 42

#eval maxVect ⟨[1, 5, 9, 20],rfl⟩
-- Output: 20


----------------------------------------------------------------------------------------------------
-- Formal Verification
----------------------------------------------------------------------------------------------------


theorem le_maxVect {n : Nat} {v : List.Vector Nat n} {x : Nat} (h : x ∈ v.toList) :
   x ≤ maxVect v := by
 induction n with
 | zero => exact absurd h (List.Vector.notMem_zero x v)
 | succ n ih =>
   rcases (List.Vector.mem_succ_iff x v).mp h with rfl | h'
   · exact Nat.le_max_left _ _
   · exact Nat.le_trans (ih h') (Nat.le_max_right _ _)


theorem maxVect_mem {n : Nat} (v : List.Vector Nat n) (h : n > 0) : maxVect v ∈ v.toList := by
  cases n with
  | zero => contradiction
  | succ n =>
    clear h
    induction n with
    | zero =>
      have h1 : maxVect v = v.head := by
        unfold maxVect
        have h_tail : maxVect v.tail = 0 := rfl
        rw [h_tail, max_eq_left (Nat.zero_le _)]
      rw [h1]
      exact List.Vector.head_mem v
    | succ n ih =>
      have h_max : maxVect v = v.head ∨ maxVect v = maxVect v.tail := by
        unfold maxVect
        exact max_choice v.head (maxVect v.tail)
      rcases h_max with h1 | h2
      · rw [h1]
        exact List.Vector.head_mem v
      · rw [h2]
        apply List.Vector.mem_of_mem_tail
        apply ih v.tail


----------------------------------------------------------------------------------------------------
-- Other implementations
----------------------------------------------------------------------------------------------------


def maxVect? : {n : Nat} → List.Vector Nat n → Option Nat
 | 0,     _ => none
 | _ + 1, v => some (v.tail.toList.foldr max v.head)


def maxVect' {n : Nat} (v : List.Vector Nat (n + 1)) : Nat :=
 match n, v with
 | 0,     v => v.head
 | _ + 1, v => max v.head (maxVect' v.tail)


end MaxVect
