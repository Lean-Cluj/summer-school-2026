/-
Copyright (c) 2026 Iulian Simion. All rights reserved.
Released under the 3-Clause BSD License as described in the file LICENSE.
Authors: Iulian Simion, assisted by Claude (Anthropic) and Gemini (Google)
-/
import Mathlib.Data.Real.Basic

/-! # Solutions — Propositions -/

-- 1
theorem ex1 : 2 + 2 = 4 := by rfl

-- 2
theorem ex2 : 3 * 4 = 4 * 3 := Nat.mul_comm 3 4

-- 3
-- The term `h1.symm` proves `x = y`, and `Eq.trans` joins it to `h2 : y = z`.
theorem ex3 (x y z : ℝ) (h1 : y = x) (h2 : y = z) : x = z := h1.symm.trans h2

-- The goal as Lean displays it:
--   x y z : ℝ
--   h1 : y = x
--   h2 : y = z
--   ⊢ x = z
-- The display omits the term. The goal is the judgment `Γ ⊢ ? : x = z`, and
-- the term still to be produced is the proof.
