/-
Copyright (c) 2026 Iulian Simion. All rights reserved.
Released under the 3-Clause BSD License as described in the file LICENSE.
Authors: Iulian Simion, assisted by Claude (Anthropic) and Gemini (Google)
-/
import Mathlib.Data.Real.Basic

/-! # Solutions — Rewriting -/

-- 1
-- The lemma is `pow_add : a ^ (m + n) = a ^ m * a ^ n`.
theorem ex1 (a m n : ℕ) (h : m = 2) : a ^ (m + n) = a ^ 2 * a ^ n :=
  by
    rw [pow_add, h]

-- 2
-- The lemma is `abs_mul : |a * b| = |a| * |b|`.
theorem ex2 (x y : ℝ) (h : |x| * |y| = 6) : |x * y| = 6 :=
  by
    rwa [abs_mul]

-- 3
theorem ex3 (a b : ℕ) (h : a = b) (h2 : b + a = 7) : a + a = 7 :=
  by
    nth_rw 1 [h]
    exact h2
