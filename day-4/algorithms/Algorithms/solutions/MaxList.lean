/-
Copyright (c) 2026 Iulian Simion. All rights reserved.
Released under the 3-Clause BSD License as described in the file LICENSE.
Authors: Iulian Simion, assisted by Claude (Anthropic) and Gemini (Google)
-/
import Algorithms.MaxList

/-! # Solutions — The maximum of a list -/

namespace MaxList.Solutions

-- 1
-- Both `m` and `maxList l` are upper bounds and members, so each is at most the other.
theorem maxList_unique {l : List Nat} {m : Nat} (hm : m ∈ l) (hub : ∀ x ∈ l, x ≤ m) :
    maxList l = m :=
  Nat.le_antisymm (hub _ (maxList_mem (List.ne_nil_of_mem hm))) (le_maxList hm)

-- 2
theorem maxList_append (l₁ l₂ : List Nat) :
    maxList (l₁ ++ l₂) = max (maxList l₁) (maxList l₂) := by
  induction l₁ with
  | nil =>
    change maxList l₂ = max 0 (maxList l₂)
    rw [Nat.zero_max]
  | cons x xs ih =>
    change max x (maxList (xs ++ l₂)) = max (max x (maxList xs)) (maxList l₂)
    rw [ih, Nat.max_assoc]

-- 3
theorem maxList'_eq (l : List Nat) : maxList' l = maxList l := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    cases xs with
    | nil =>
      change x = max x 0
      rw [Nat.max_zero]
    | cons y ys =>
      change max x (maxList' (y :: ys)) = max x (maxList (y :: ys))
      rw [ih]

end MaxList.Solutions
