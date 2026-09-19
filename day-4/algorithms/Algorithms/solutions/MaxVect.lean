/-
Copyright (c) 2026 Iulian Simion. All rights reserved.
Released under the 3-Clause BSD License as described in the file LICENSE.
Authors: Iulian Simion, assisted by Claude (Anthropic) and Gemini (Google)
-/
import Algorithms.MaxVect

/-! # Solutions — The maximum of a vector -/

namespace MaxVect.Solutions

-- 1
theorem maxVect'_mem {n : Nat} (v : List.Vector Nat (n + 1)) : maxVect' v ∈ v.toList := by
  induction n with
  | zero =>
    change v.head ∈ v.toList
    exact List.Vector.head_mem v
  | succ n ih =>
    change max v.head (maxVect' v.tail) ∈ v.toList
    rcases max_choice v.head (maxVect' v.tail) with h1 | h2
    · rw [h1]
      exact List.Vector.head_mem v
    · rw [h2]
      exact List.Vector.mem_of_mem_tail _ v (ih v.tail)

-- 2
theorem le_maxVect' {n : Nat} {v : List.Vector Nat (n + 1)} {x : Nat} (h : x ∈ v.toList) :
    x ≤ maxVect' v := by
  induction n with
  | zero =>
    change x ≤ v.head
    rcases (List.Vector.mem_succ_iff x v).mp h with rfl | h'
    · exact Nat.le_refl _
    · exact absurd h' (List.Vector.notMem_zero x v.tail)
  | succ n ih =>
    change x ≤ max v.head (maxVect' v.tail)
    rcases (List.Vector.mem_succ_iff x v).mp h with rfl | h'
    · exact Nat.le_max_left _ _
    · exact Nat.le_trans (ih h') (Nat.le_max_right _ _)

-- 3
theorem maxVect'_eq {n : Nat} (v : List.Vector Nat (n + 1)) : maxVect' v = maxVect v := by
  induction n with
  | zero =>
    change v.head = max v.head 0
    rw [Nat.max_zero]
  | succ n ih =>
    change max v.head (maxVect' v.tail) = max v.head (maxVect v.tail)
    exact congrArg (max v.head) (ih v.tail)

end MaxVect.Solutions
