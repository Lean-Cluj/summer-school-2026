/-
Copyright (c) 2026 Iulian Simion. All rights reserved.
Released under the 3-Clause BSD License as described in the file LICENSE.
Authors: Iulian Simion, assisted by Claude (Anthropic) and Gemini (Google)
-/
import Mathlib.Data.Real.Basic
import Mathlib.Data.Int.ModEq
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.GCongr

/-! # Solutions — Inequalities and congruences -/

-- 1
-- The tactic `linarith` does not prove it: `x ^ 3` and `x ^ 2` are non-linear
-- terms, so it treats each as an opaque atom and has no fact about either.
theorem ex1 (x : ℤ) (hx : x ≥ 3) : 2 * x ^ 3 - 4 * x ^ 2 + 3 * x ≥ 3 :=
  calc
    2 * x ^ 3 - 4 * x ^ 2 + 3 * x
        = 2 * x * x ^ 2 - 4 * x ^ 2 + 3 * x := by ring
    _ ≥ 2 * 3 * x ^ 2 - 4 * x ^ 2 + 3 * x := by rel [hx]
    _ = 2 * x ^ 2 + 3 * x := by ring
    _ ≥ 2 * 3 ^ 2 + 3 * 3 := by rel [hx]
    _ ≥ 3 := by norm_num

-- 2
theorem ex2 (x : ℝ) (hx : 0 < x) : 0 < x ^ 3 + x :=
  by positivity

-- 3
-- The last step is a congruence between numerals, `12 ≡ 2 [ZMOD 5]`, which
-- `rfl` settles by computation since both sides reduce to `2`.
theorem ex3 (a b : ℤ) (ha : a ≡ 4 [ZMOD 5]) (hb : b ≡ 3 [ZMOD 5]) :
    a * b ≡ 2 [ZMOD 5] :=
  calc a * b ≡ 4 * b [ZMOD 5] := by rel [ha]
    _ ≡ 4 * 3 [ZMOD 5] := by rel [hb]
    _ ≡ 2 [ZMOD 5] := rfl
