/-
Copyright (c) 2026 Iulian Simion. All rights reserved.
Released under the 3-Clause BSD License as described in the file LICENSE.txt.
Authors: Iulian Simion
-/
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-
  EXAMPLE 1 (ring)
-/
example (a b : ℝ) : (a + b) * (a + b) = a * a + 2 * (a * b) + b * b :=
  by
    calc
      (a + b) * (a + b) = (a + b) * a + (a + b) * b := by rw [mul_add]
      _ = (a * a + b * a) + (a+b) * b := by rw [add_mul]
      _ = (a * a + b * a) + (a * b + b * b) := by rw [add_mul]
      _ = a * a + (b * a + a * b) + b * b := by rw [← add_assoc, add_assoc (a * a)]
      _ = a * a + 2 * (a * b) + b * b := by rw [mul_comm b a, ← two_mul]

-- or

example (a b : ℝ) : (a + b) * (a + b) = a * a + 2 * (a * b) + b * b := by ring

/-
  EXAMPLE 2 (integers)
-/
example (m : ℤ) (hm : 10 + m = 9) : 2 * m ≠ -3 :=
  by
    apply ne_of_gt
    have h: m = -1 :=
      calc
        m = 10 + m - 10 := by ring
        _ = 9 - 10 := by rw [hm]
    calc
      2 * m = 2 * (-1) := by rw [h]
      _ > -3 := by linarith

/-
  EXERCISE
-/
#check ne_of_lt
example {m : ℤ} (hm : 10 + m = 7) : 3 * m ≠ -2 :=
  by
    apply ne_of_lt
    have h: m = -3 :=
      calc
        m = 10 + m - 10 := by ring
        _ = 7 - 10 := by rw [hm]
    calc
      3 * m = 3 * (-3) := by rw [h]
      _ < -2 := by norm_num1

/-
  EXAMPLE 3 (inequalities)
-/
example (a b : ℝ) : 2*a*b ≤ a^2 + b^2 := by
  have h : 0 ≤ a^2 - 2*a*b + b^2 := by
    calc
      a^2 - 2*a*b + b^2 = (a - b)^2 := by ring
      _ ≥ 0 := by apply sq_nonneg
  calc
    2*a*b = 2*a*b := by ring
    _ ≤ 2*a*b + (a^2 - 2*a*b + b^2) := le_add_of_nonneg_right h  --add_le_add (le_refl _) h
    _ = a^2 + b^2 := by ring

-- or

example (a b : ℝ) : 2*a*b ≤ a^2 + b^2 := by
  have h : 0 ≤ a^2 - 2*a*b + b^2 := by
    calc
      a^2 - 2*a*b + b^2 = (a - b)^2 := by ring
      _ ≥ 0 := by apply pow_two_nonneg
  linarith -- this is a linear step

/-
  EXAMPLE 4 (inside `calc`)
-/
lemma extra_square {a b x : ℝ} (ha : a ≥ 0) : a * x^2 + b ≥ b := by
  have h_sq : 0 ≤ a * x^2 := by positivity
  linarith

example (x : ℝ) (hx : x ≥ 3) : 2 * x ^ 3 - 4 * x ^ 2 + 3 * x ≥ 3 :=
  by
    have h : (2 : ℝ) ≥ 0 := by norm_num
    calc
      2 * x ^ 3 - 4 * x ^ 2 + 3 * x
        = 2 * x * x ^ 2 - 4 * x ^ 2 + 3 * x := by ring
      _ ≥ 2 * 3 * x ^ 2 - 4 * x ^ 2 + 3 * x := by rel [hx]
      _ = 2 * x^2 + 3 * x := by ring
      _ ≥ 3 * x := extra_square h -- above lemma or `by nlinarith`
      _ ≥ 3 * 3 := by rel [hx]
      _ ≥ 3 := by norm_num1

/-
  EXERCISE
-/
example (x : ℝ) (hx : x ≥ 9) : x ^ 3 - 8 * x ^ 2 + 2 * x ≥ 3 :=
  by
    have h : (1 : ℝ) ≥ 0 := by norm_num
    calc
      x ^ 3 - 8 * x ^ 2 + 2 * x
        = x * x^2 - 8 * x^2 + 2 * x := by ring
      _ ≥ 9 * x^2 - 8 * x^2 + 2 * x := by rel [hx]
      _ = 1 * x^2 + 2 * x := by ring
      _ ≥ 2 * x := extra_square h -- above lemma or `by nlinarith`
      _ ≥ 2 * 9 := by rel [hx]
      _ ≥ 3 := by norm_num1
