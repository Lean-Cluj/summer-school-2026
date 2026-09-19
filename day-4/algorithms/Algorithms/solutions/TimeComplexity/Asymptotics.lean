/-
Copyright (c) 2026 Iulian Simion. All rights reserved.
Released under the 3-Clause BSD License as described in the file LICENSE.
Authors: Iulian Simion, assisted by Claude (Anthropic) and Gemini (Google)
-/
import Algorithms.TimeComplexity.Asymptotics

/-! # Solutions — Asymptotic growth -/

open Asymptotics Filter Growth

namespace BigOExamples.Solutions

-- 1
-- From `n = 1` on, `1 ≤ 1 * n`.
theorem const_isBigO_linear : const ∈ O(linear) := by
  apply IsBigO.of_bound 1
  rw [Filter.eventually_atTop]
  use 1
  intro n hn
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  simp only [const, linear, Pi.one_apply, norm_one, Real.norm_eq_abs, one_mul]
  rw [abs_of_nonneg (by positivity)]
  exact hn'

-- 2
theorem sq_add_isBigO_quadratic : (fun n : ℕ => (n : ℝ) ^ 2 + 4 * n) ∈ O(quadratic) :=
  (isBigO_refl quadratic atTop).add
    (((isBigO_refl linear atTop).const_mul_left 4).trans linear_isBigO_quadratic)

-- 3
lemma double_eq (n : ℕ) : double n = 2 * n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [double, ih]
    ring

theorem double_isBigO_linear : (fun n => (double n : ℝ)) ∈ O(linear) := by
  have h : (fun n => (double n : ℝ)) = fun n => 2 * linear n := by
    ext n
    simp [double_eq, linear]
  rw [h]
  exact (isBigO_refl linear atTop).const_mul_left 2

end BigOExamples.Solutions
