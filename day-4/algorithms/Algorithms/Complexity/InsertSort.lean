/-
  TODO:
  Clean this up
-/

import Cslib.Algorithms.Lean.TimeM
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Log

import Algorithms.Complexity.Asymptotics

open Cslib.Algorithms.Lean
open Asymptotics Filter

def insertT (x : Nat) : List Nat → TimeM Nat (List Nat)
  | []      => pure [x]
  | y :: ys => do
      ✓                                  -- compare x ≤ y
      if x ≤ y then pure (x :: y :: ys)
      else do
        let zs ← insertT x ys
        pure (y :: zs)

def isortT : List Nat → TimeM Nat (List Nat)
  | []      => pure []
  | x :: xs => do
      let ys ← isortT xs
      insertT x ys


def insertCost (x : Nat) (l : List Nat) : Nat := (insertT x l).time
def isortCost (l : List Nat) : Nat := (isortT l).time

theorem insertT_ret_length (x : Nat) (l : List Nat) : (insertT x l).ret.length = l.length + 1 := by
  induction l with
  | nil => rfl
  | cons y ys ih =>
    have step : (insertT x (y :: ys)).ret = (if x ≤ y then pure (x :: y :: ys) else do let zs ← insertT x ys; pure (y :: zs)).ret := by rfl
    rw [step]
    split
    · rfl
    · have h2 : ((do let zs ← insertT x ys; pure (y :: zs)) : TimeM Nat (List Nat)).ret = y :: (insertT x ys).ret := by rfl
      rw [h2]
      simp [ih]

theorem isortT_ret_length (l : List Nat) : (isortT l).ret.length = l.length := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    have step : (isortT (x :: xs)).ret = (insertT x (isortT xs).ret).ret := by rfl
    rw [step, insertT_ret_length, ih]
    rfl

theorem insertCost_le (x : Nat) (l : List Nat) : insertCost x l ≤ l.length := by
  induction l with
  | nil => rfl
  | cons y ys ih =>
    change (insertT x (y :: ys)).time ≤ (y :: ys).length
    have h1 : (insertT x (y :: ys)).time = 1 + (if x ≤ y then pure (x :: y :: ys) else do let zs ← insertT x ys; pure (y :: zs)).time := by rfl
    rw [h1]
    split
    · exact Nat.le_add_left 1 ys.length
    · have h2 : ((do let zs ← insertT x ys; pure (y :: zs)) : TimeM Nat (List Nat)).time = (insertT x ys).time := by rfl
      rw [h2]
      change (insertT x ys).time ≤ ys.length at ih
      have h3 : (y :: ys).length = ys.length + 1 := by rfl
      rw [h3]
      omega

theorem isortCost_le (l : List Nat) : isortCost l ≤ l.length ^ 2 := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    change (isortT (x :: xs)).time ≤ (x :: xs).length ^ 2
    change (isortT xs).time ≤ xs.length ^ 2 at ih
    have h1 : (isortT (x :: xs)).time = (isortT xs).time + (insertT x (isortT xs).ret).time := by rfl
    rw [h1]
    have h2 : (insertT x (isortT xs).ret).time ≤ (isortT xs).ret.length := insertCost_le x (isortT xs).ret
    change (insertT x (isortT xs).ret).time ≤ (isortT xs).ret.length at h2
    rw [isortT_ret_length] at h2
    have h3 : (x :: xs).length = xs.length + 1 := by rfl
    rw [h3]
    nlinarith



/-- Phase 1: a linear scan, `2n + 1` steps. -/
def phase₁Time (n : ℕ) : ℝ := 2 * n + 1

/-- Phase 2: a quadratic pass, `n² + 3n` steps. -/
def phase₂Time (n : ℕ) : ℝ := n * n + 3 * n

/-! ## §3. The individual bounds, proved by hand

Each of these needs a constant and a threshold. Note that `isBigO_of_le` would
*fail* on both: at `n = 0` phase 1 costs `1` while `linear 0 = 0`, so no
pointwise bound with constant `1` exists. This is exactly the situation the
`atTop` filter is designed for. -/

theorem phase₁_isBigO_linear : phase₁Time =O[atTop] Growth.linear := by
  refine IsBigO.of_bound 3 ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn' : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  simp only [phase₁Time, Growth.linear]
  rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity)]
  linarith

theorem phase₂_isBigO_quadratic : phase₂Time =O[atTop] Growth.quadratic := by
  refine IsBigO.of_bound 4 ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn' : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  simp only [phase₂Time, Growth.quadratic]
  rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity)]
  nlinarith

/-- Linear growth is dominated by quadratic growth. This is the `trans` step:
it lets a phase analysed as `O(n)` be reused inside an `O(n²)` argument. -/
theorem isBigO_linear_quadratic : Growth.linear =O[atTop] Growth.quadratic := by
  refine IsBigO.of_bound 1 ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn' : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  simp only [Growth.linear, Growth.quadratic]
  rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity)]
  nlinarith

/-! ## §4. The payoff

No constant, no threshold, no `filter_upwards`. The bound for the composite
follows from the algebra of `IsBigO` alone. -/

theorem twoPhase_isBigO :
    (fun n => phase₁Time n + phase₂Time n) ∈ O(Growth.quadratic) :=
  (phase₁_isBigO_linear.trans isBigO_linear_quadratic).add phase₂_isBigO_quadratic
