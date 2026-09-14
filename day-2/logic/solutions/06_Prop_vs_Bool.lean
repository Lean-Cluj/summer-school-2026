/-
Copyright (c) 2026 Iulian Simion. All rights reserved.
Released under the 3-Clause BSD License as described in the file LICENSE.
Authors: Iulian Simion, assisted by Claude (Anthropic) and Gemini (Google)
-/
import Mathlib.Tactic.NormNum
import Mathlib.Data.Real.Basic

/-! # Solutions — `Prop` and `Bool` -/

-- 1
theorem ex1 : ∀ n : Fin 4, n.val + 1 ≤ 4 := by decide

-- 2
theorem ex2 : (123456 : ℝ) * 654321 = 80779853376 := by norm_num
-- Equality on `ℝ` does have a `Decidable` instance, but it is the classical one
-- of `05_Classical_Logic.lean`: it is built from `Classical.choice`, so there is
-- nothing for `decide` to run and it gets stuck (the error message says so).
-- The tactic `norm_num` reasons about the numerals instead of evaluating them,
-- so it is unaffected.
-- (Over `ℕ` the same statement *is* decidable, and `by decide` closes it.)
example : 123456 * 654321 = 80779853376 := by decide

-- 3
def evenB : ℕ → Bool
  | 0 => true
  | 1 => false
  | n + 2 => evenB n

#eval evenB 10
#eval evenB 7

-- An equation between two concrete `Bool` values: both sides evaluate, so
-- `rfl` proves it.
theorem ex3 : evenB 10 = true := rfl
