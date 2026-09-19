/-
Copyright (c) 2026 Iulian Simion. All rights reserved.
Released under the 3-Clause BSD License as described in the file LICENSE.
Authors: Iulian Simion, assisted by Claude (Anthropic) and Gemini (Google)
-/
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

/-! # Solutions — Calculation -/

-- 1
theorem ex1 (p q r s : ℝ) : p * (q + r) * s = p * (r * s) + p * (q * s) :=
  by
    rw [mul_add, add_mul, mul_assoc, mul_assoc, add_comm]

theorem ex1' (p q r s : ℝ) : p * (q + r) * s = p * (r * s) + p * (q * s) :=
  by ring

-- 2
-- The tactic `ring` proves equations only, and this is a strict inequality
-- between numerals, which `norm_num` proves.
theorem ex2 : (3 : ℝ) / 7 < 1 / 2 :=
  by norm_num

-- 3
theorem ex3 (x y : ℝ) (h1 : 2 * x + 3 * y = 12) (h2 : y = 2) : x = 3 :=
  calc
    x = ((2 * x + 3 * y) - 3 * y) / 2 := by ring
    _ = (12 - 3 * 2) / 2 := by rw [h1, h2]
    _ = 3 := by norm_num
