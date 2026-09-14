/-
Copyright (c) 2026 Iulian Simion. All rights reserved.
Released under the 3-Clause BSD License as described in the file LICENSE.
Authors: Iulian Simion, assisted by Claude (Anthropic) and Gemini (Google)
-/
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring

/-! # Solutions — Combinators and macros -/

namespace CombinatorExercises

inductive Even : ℕ → Prop where
  | zero : Even 0
  | add_two : ∀ k : ℕ, Even k → Even (k + 2)

/-! ## Exercises of `07_Tactic_Combinators.lean` -/

-- 1
-- The tactic `constructor` picks whichever constructor of `Even` applies, so
-- no tactic has to be written twice.
theorem ex1 : Even 6 :=
  by repeat' constructor

-- naming the constructors explicitly also works
example : Even 6 :=
  by
    repeat'
      first
      | apply Even.add_two
      | apply Even.zero

-- 2
theorem ex2 (n : ℕ) (h : n = 1 ∨ n = 3 ∨ n = 5) : n % 2 = 1 :=
  by rcases h with h | h | h <;> omega

/-! ## Exercise of `08_Macros.lean` -/

namespace Macros

-- 1
macro "even_search" : tactic =>
  `(tactic|
      (repeat'
        first
        | apply Even.add_two
        | apply Even.zero))

theorem ex1 : Even 10 := by even_search

end Macros

end CombinatorExercises
