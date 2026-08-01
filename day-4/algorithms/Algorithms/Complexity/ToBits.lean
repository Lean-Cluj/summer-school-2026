import Cslib.Algorithms.Lean.TimeM
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Log
import Algorithms.Complexity.Asymptotics

open Cslib.Algorithms.Lean
open Asymptotics Filter

namespace ToBits

----------------------------------------------------------------------------------------------------
-- Natural number to binary representation using TimeM
----------------------------------------------------------------------------------------------------

def toBitsTM (n : Nat) : TimeM Nat (List Bool) :=
  if h : n = 0 then
    pure []
  else
    have h_term : n / 2 < n := Nat.div_lt_self (by omega) (by decide)
    do
      TimeM.tick 1
      let rest ← toBitsTM (n / 2)
      pure ((n % 2 == 1) :: rest)
termination_by n


----------------------------------------------------------------------------------------------------
-- Closed form of the time function for toBitsTM
----------------------------------------------------------------------------------------------------


def toBitsTimeFunction (n : ℕ) : ℝ := Nat.log2 n + 1

theorem toBitsTimeFunction_correct (n : Nat) (hN : n > 0) :
  (toBitsTM n).time = toBitsTimeFunction n := by
  unfold toBitsTM
  split
  · omega
  · rename_i h_neq
    have h_one_le : 1 ≤ n := by omega
    rcases eq_or_lt_of_le h_one_le with rfl | hn_gt_one
    · -- Subcase: n = 1
      have h_half : 1 / 2 = 0 := rfl
      unfold toBitsTM
      simp [toBitsTimeFunction]
    · -- Subcase: n ≥ 2
      have h_half_pos : n / 2 > 0 := by omega
      have ih := toBitsTimeFunction_correct (n / 2) h_half_pos
      -- Use Lean core's built-in unfolding definition for Nat.log2
      have h_log : (Nat.log2 n : ℝ) = (Nat.log2 (n / 2) : ℝ) + 1 := by
        have h_ge : 2 ≤ n := hn_gt_one
        have h_log_nat : Nat.log2 n = Nat.log2 (n / 2) + 1 := by
          rw [Nat.log2_def]
          simp [h_ge]
        exact_mod_cast h_log_nat
      simp [ih, toBitsTimeFunction, h_log]
      ring


----------------------------------------------------------------------------------------------------
-- Big-O formulation of the time complexity for toBitsTM
----------------------------------------------------------------------------------------------------


theorem toBitsTimeFunction_isBigO_logarithmic : toBitsTimeFunction ∈ O(Growth.logarithmic) := by
  refine IsBigO.of_bound (2 / Real.log 2) ?_
  filter_upwards [eventually_ge_atTop 2] with n hn
  have hn2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have h_log_mono := Real.log_le_log (by norm_num) hn2
  have h_log2_pos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  -- We need to prove `‖toBitsTimeFunction n‖ ≤ (2 / Real.log 2) * ‖Growth.logarithmic n‖`
  simp only [toBitsTimeFunction, Growth.logarithmic, Real.norm_eq_abs]
  have h_log2_nonneg : (0 : ℝ) ≤ Nat.log2 n := Nat.cast_nonneg _
  have h_pos : (0 : ℝ) ≤ (Nat.log2 n : ℝ) + 1 := by positivity
  rw [abs_of_nonneg h_pos]
  have h_log_pos : (0 : ℝ) ≤ Real.log (n : ℝ) := h_log_mono.trans' (Real.log_pos (by norm_num)).le
  rw [abs_of_nonneg h_log_pos]
  have hn_ne_zero : n ≠ 0 := by omega
  have h_pow : 2 ^ Nat.log 2 n ≤ n := Nat.pow_log_le_self 2 hn_ne_zero
  have h_log2_eq : Nat.log2 n = Nat.log 2 n := Nat.log2_eq_log_two
  rw [h_log2_eq]
  have h_pow_real : (2 : ℝ) ^ (Nat.log 2 n : ℕ) ≤ (n : ℝ) := by exact_mod_cast h_pow
  -- Take Real.log of both sides
  have h_log_pow := Real.log_le_log (by positivity) h_pow_real
  -- Real.log (2^k) = k * Real.log 2
  have h_log_pow_eq : Real.log ((2 : ℝ) ^ (Nat.log 2 n : ℕ)) = (Nat.log 2 n : ℝ) * Real.log 2 := by
    rw [Real.log_pow]
  rw [h_log_pow_eq] at h_log_pow
  -- Now divide by Real.log 2
  have h_log2_le : (Nat.log 2 n : ℝ) ≤ Real.log (n : ℝ) / Real.log 2 := by
    rw [le_div_iff₀ h_log2_pos]
    exact h_log_pow
  -- We also have 1 ≤ Real.log n / Real.log 2 for n ≥ 2
  have h_one_le : (1 : ℝ) ≤ Real.log (n : ℝ) / Real.log 2 := by
    rw [le_div_iff₀ h_log2_pos]
    rw [one_mul]
    exact h_log_mono
  calc
    (Nat.log 2 n : ℝ) + 1 ≤ Real.log (n : ℝ) / Real.log 2 + Real.log (n : ℝ) / Real.log 2 :=
    add_le_add h_log2_le h_one_le
    _ = (2 / Real.log 2) * Real.log (n : ℝ) := by ring

end ToBits
