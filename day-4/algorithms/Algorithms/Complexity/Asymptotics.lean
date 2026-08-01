import Mathlib.Data.Vector.Basic
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.SpecialFunctions.Log.Basic -- Required for Real.log


open Asymptotics Filter

/-- The set of functions growing no faster than `g`, asymptotically. -/
abbrev BigO (g : ℕ → ℝ) : Set (ℕ → ℝ) := {f | f =O[atTop] g}

notation "O(" g ")" => BigO g

example (f g : ℕ → ℝ) (h : f =O[atTop] g) : f ∈ O(g) := h
example (f g : ℕ → ℝ) (h : f ∈ O(g)) : f =O[atTop] g := h

example {f g h : ℕ → ℝ} (h1 : f ∈ O(g)) (h2 : g ∈ O(h)) : f ∈ O(h) :=
  h1.trans h2


----------------------------------------------------------------------------------------------------
-- Complexity classes for common growth rates
----------------------------------------------------------------------------------------------------


namespace Growth


/-- Constant growth. -/
def const : ℕ → ℝ := 1

/-- Linear growth: `n ↦ n`. -/
def linear : ℕ → ℝ := Nat.cast

/-- Quadratic growth: `n ↦ n²`. -/
def quadratic : ℕ → ℝ := fun n => (n : ℝ) ^ 2

/-- Logarithmic growth: `n ↦ ln n`. -/
noncomputable def logarithmic : ℕ → ℝ := fun n => Real.log (n : ℝ)

/-- Exponential growth: `n ↦ 2ⁿ`. -/
def exponential : ℕ → ℝ := fun n => (2 : ℝ) ^ n


end Growth


open Growth


----------------------------------------------------------------------------------------------------
-- Examples for the linear class
----------------------------------------------------------------------------------------------------

namespace LinearClassExamples

example : linear ∈ O(linear) :=
  isBigO_refl linear atTop

def f : ℕ → ℝ := fun n => 3 * n

example : f ∈ O(linear) :=
  (isBigO_refl linear atTop).const_mul_left 3

def g : ℕ → ℝ := fun n => 5 * n + 2 * n

example : g ∈ O(linear) := by
  have h_left : (fun n => 5 * linear n) ∈ O(linear) :=
    (isBigO_refl linear atTop).const_mul_left 5
  have h_right : (fun n => 2 * linear n) ∈ O(linear) :=
    (isBigO_refl linear atTop).const_mul_left 2
  exact h_left.add h_right

end LinearClassExamples

----------------------------------------------------------------------------------------------------
-- Examples: Working with bounds and filters
----------------------------------------------------------------------------------------------------

def my_bound (f : ℕ → ℝ) : Prop := ∀ n, ‖f n‖ ≤ 5 * ‖linear n‖

example {f : ℕ → ℝ} (hf : my_bound f) : f ∈ O(linear) := by
  apply IsBigO.of_bound 5
  exact Eventually.of_forall hf

def delayed_linear (n : ℕ) : ℝ :=
  if n < 100 then
    (n : ℝ) ^ 3
  else
    (n : ℝ)

example : delayed_linear ∈ O(linear) := by
  apply IsBigO.of_bound 1
  rw [Filter.eventually_atTop]
  use 100
  intro n hn
  have h_not : ¬(n < 100) := by omega
  simp only [delayed_linear, linear, if_neg h_not, one_mul, le_refl]


----------------------------------------------------------------------------------------------------
-- Examples: quadratic, logarithmic, and exponential classes
----------------------------------------------------------------------------------------------------

namespace QuadraticLogarithmicExponentialExamples

def f : ℕ → ℝ := fun n => 3 * n ^ 2 + 2 * n

-- Helper: `n` grows no faster than `n²`, needed to bound the linear term below.
lemma linear_isBigO_quadratic : linear ∈ O(quadratic) := by
  apply IsBigO.of_bound 1
  rw [Filter.eventually_atTop]
  use 1
  intro n hn
  simp only [linear, quadratic, one_mul, Real.norm_eq_abs]
  rw [abs_of_pos (by positivity), abs_of_pos (by positivity)]
  have hn_real : (1 : ℝ) ≤ n := by exact_mod_cast hn
  nlinarith

example : f ∈ O(quadratic) := by
  have h_quad : (fun n => 3 * quadratic n) ∈ O(quadratic) :=
    (isBigO_refl quadratic atTop).const_mul_left 3
  have h_lin : (fun n => 2 * linear n) ∈ O(quadratic) :=
    ((isBigO_refl linear atTop).const_mul_left 2).trans linear_isBigO_quadratic
  exact h_quad.add h_lin



noncomputable def g : ℕ → ℝ := fun n => Real.log (n : ℝ) / Real.log 2

example : g ∈ O(logarithmic) := by
  have h_eq : g = fun n => (1 / Real.log 2) * logarithmic n := by
    ext n
    simp only [g, logarithmic]
    ring_nf
  rw [h_eq]
  exact (isBigO_refl logarithmic atTop).const_mul_left (1 / Real.log 2)


example : (fun n => (2 : ℝ) ^ (n + 3)) ∈ O(exponential) := by
  have h_eq : (fun n => (2 : ℝ) ^ (n + 3)) = (fun n => 2^3 * exponential n) := by
    ext n
    simp only [exponential]
    rw [pow_add]
    ring
  rw [h_eq]
  exact (isBigO_refl exponential atTop).const_mul_left ((2:ℝ)^3)

end QuadraticLogarithmicExponentialExamples

/-
----------------------------------------------------------------------------------------------------
Example: recursive complexity proofs (Quadratic)

A Recursive Sum (Quadratic Time)
Consider a function that adds `n` at each step. To a beginner, the single `+ n`
might look linear, but it evaluates to the triangular numbers `n(n+1)/2`.

Instead of finding the exact closed form, we can prove a loose
upper bound directly by induction.
----------------------------------------------------------------------------------------------------
-/


def recSum : ℕ → ℕ
| 0 => 0
| (n + 1) => recSum n + (n + 1)

lemma recSum_bound (n : ℕ) : recSum n ≤ n ^ 2 := by
  induction n with
  | zero => decide
  | succ k ih =>
    unfold recSum
    calc
      recSum k + (k + 1) ≤ k ^ 2 + (k + 1) := Nat.add_le_add_right ih (k + 1)
      _                  ≤ (k + 1) ^ 2     := by nlinarith

example : (fun n => (recSum n : ℝ)) ∈ O(quadratic) := by
  apply IsBigO.of_bound 1
  rw [Filter.eventually_atTop]
  use 0
  intro n _
  simp only [quadratic, one_mul]
  have h_pos1 : (0 : ℝ) ≤ recSum n := Nat.cast_nonneg _
  have h_pos2 : (0 : ℝ) ≤ (n : ℝ) ^ 2 := by positivity
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg h_pos1, abs_of_nonneg h_pos2]
  exact_mod_cast recSum_bound n


/-
----------------------------------------------------------------------------------------------------
Example: recursive complexity proofs (Exponential)

Consider a Tower of Hanoi-style algorithm: T(0)=1, T(n+1) = 2*T(n) + 1.
This is a classic trap for students. If they try to prove the loose bound
`hanoi n ≤ 2^(n+1)` by direct induction, the step fails mathematically:
2*(2^(k+1)) + 1 is NOT ≤ 2^(k+2).

Sometimes you must *strengthen the induction hypothesis* by
proving the exact closed form first.
----------------------------------------------------------------------------------------------------
-/


def hanoi : ℕ → ℕ
| 0 => 1
| (n + 1) => 2 * hanoi n + 1

lemma hanoi_closed_form (n : ℕ) : hanoi n + 1 = 2 ^ (n + 1) := by
  induction n with
  | zero => rfl
  | succ k ih =>
    unfold hanoi
    omega

lemma hanoi_upper_bound (n : ℕ) : hanoi n ≤ 2 * 2 ^ n := by
  have h : hanoi n + 1 = 2 * 2 ^ n := by
    calc hanoi n + 1 = 2 ^ (n + 1) := hanoi_closed_form n
    _                = 2 * 2 ^ n   := by ring
  omega

example : (fun n => (hanoi n : ℝ)) ∈ O(exponential) := by
  apply IsBigO.of_bound 2
  rw [Filter.eventually_atTop]
  use 0
  intro n _
  simp only [exponential]
  have h_pos1 : (0 : ℝ) ≤ hanoi n := Nat.cast_nonneg _
  have h_pos2 : (0 : ℝ) ≤ (2 : ℝ) ^ n := by positivity
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg h_pos1, abs_of_nonneg h_pos2]
  exact_mod_cast hanoi_upper_bound n


/-
----------------------------------------------------------------------------------------------------
Example: recursive complexity proofs (Logarithmic)

Counting Bits / Binary Search Depth.
A recursively defined function that halves its input at each step.
----------------------------------------------------------------------------------------------------
-/


def logRec (n : ℕ) : ℕ :=
  if n = 0 then 0
  else logRec (n / 2) + 1
termination_by n
decreasing_by omega

lemma logRec_pow_bound (n : ℕ) (hn : 1 ≤ n) : 2 ^ logRec n ≤ 2 * n := by
  if h2 : n / 2 = 0 then
    -- Base case: If n/2 = 0 but 1 ≤ n, then n must be 1.
    have hn1 : n = 1 := by omega
    subst hn1
    have h_logRec_1 : logRec 1 = 1 := by
      rw [logRec]
      have h1 : 1 / 2 = 0 := rfl
      rw [h1, logRec]
      rfl
    rw [h_logRec_1]
    rfl
  else
    have h_pos : 1 ≤ n / 2 := by omega
    have ih := logRec_pow_bound (n / 2) h_pos
    have h_step : logRec n = logRec (n / 2) + 1 := by
      have h_not_zero : n ≠ 0 := by omega
      rw [logRec]
      simp [h_not_zero]
    rw [h_step]
    calc 2 ^ (logRec (n / 2) + 1) = 2 ^ logRec (n / 2) * 2 := rfl
    _ ≤ (2 * (n / 2)) * 2 := Nat.mul_le_mul_right 2 ih
    _ ≤ 2 * n := by omega


lemma logRec_real_bound (n : ℕ) (hn : 1 ≤ n) :
    (logRec n : ℝ) ≤ 1 + (1 / Real.log 2) * Real.log (n : ℝ) := by
  have h_pow := logRec_pow_bound n hn
  have h_pow_R : ((2 ^ logRec n : ℕ) : ℝ) ≤ ((2 * n : ℕ) : ℝ) := by exact_mod_cast h_pow
  have h_lhs : ((2 ^ logRec n : ℕ) : ℝ) = (2 : ℝ) ^ logRec n := by norm_cast
  have h_rhs : ((2 * n : ℕ) : ℝ) = 2 * (n : ℝ) := by norm_cast
  rw [h_lhs, h_rhs] at h_pow_R
  have h_log := Real.log_le_log (by positivity) h_pow_R
  rw [Real.log_pow] at h_log
  have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  rw [Real.log_mul (by positivity) hn_pos.ne'] at h_log
  calc
    (logRec n : ℝ) = (logRec n * Real.log 2) * (1 / Real.log 2) := by
      rw [mul_assoc, one_div, mul_inv_cancel₀ (Real.log_pos (by norm_num)).ne', mul_one]
    _ ≤ (Real.log 2 + Real.log (n : ℝ)) * (1 / Real.log 2) :=
    mul_le_mul_of_nonneg_right h_log (by positivity)
    _ = 1 + (1 / Real.log 2) * Real.log (n : ℝ) := by
      rw [add_mul, one_div, mul_inv_cancel₀ (Real.log_pos (by norm_num)).ne', mul_comm]


example : (fun n => (logRec n : ℝ)) ∈ O(logarithmic) := by
  -- We provide a constant that can absorb both the logarithm and the `1 + ` offset.
  apply IsBigO.of_bound (2 / Real.log 2)
  rw [Filter.eventually_atTop]
  use 2
  intro n hn
  have hn1 : 1 ≤ n := by omega
  have h_bound := logRec_real_bound n hn1
  have hn2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have h_log_mono := Real.log_le_log (by norm_num) hn2
  have h_log2_pos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have h_one_le : (1 : ℝ) ≤ (1 / Real.log 2) * Real.log (n : ℝ) := by
    calc (1 : ℝ) = (1 / Real.log 2) * Real.log 2 := by rw [one_div, inv_mul_cancel₀ h_log2_pos.ne']
    _ ≤ (1 / Real.log 2) * Real.log (n : ℝ) := mul_le_mul_of_nonneg_left h_log_mono (by positivity)
  have h_logRec_pos : (0 : ℝ) ≤ logRec n := Nat.cast_nonneg _
  have h_log_pos : (0 : ℝ) ≤ Real.log (n : ℝ) := h_log_mono.trans' (Real.log_pos (by norm_num)).le
  simp only [logarithmic, Real.norm_eq_abs, abs_of_nonneg h_logRec_pos, abs_of_nonneg h_log_pos]
  calc
    (logRec n : ℝ) ≤ 1 + (1 / Real.log 2) * Real.log (n : ℝ) := h_bound
    _ ≤ (1 / Real.log 2) * Real.log (n : ℝ) + (1 / Real.log 2) * Real.log (n : ℝ) :=
    by linarith [h_one_le]
    _ = (2 / Real.log 2) * Real.log (n : ℝ) := by ring
