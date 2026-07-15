/-
Copyright (c) 2026 Iulian Simion. All rights reserved.
Released under the 3-Clause BSD License as described in the file LICENSE.txt.
Authors: Iulian Simion
-/
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Cases --- for induction'



example (b : Bool) : b = true ∨ b = false := by
  induction' b
  · right; rfl
  · left; rfl

example (b : Bool) : b = true ∨ b = false := by
  induction b
  · right; rfl
  · left; rfl

/- # Simple Induction
  Roughly, constructing a proof is equivalent to defining a function
  from the proofs of the assumptions to the proof of the conclusion.
-/

/- ## Simple induction on ℕ - first example -/

/- EXAMPLE 1
  We need to show that for each n ∈ ℕ a certain proposition holds.
-/
example (n : ℕ) : 2 ^ n ≥ n + 1 := by
  induction n with
  | zero =>
    -- q ^ 0 = 1
    norm_num
  | succ k IH =>
    calc 2 ^ (k + 1) = 2 * 2 ^ k := by ring
      _ ≥ 2 * (k + 1) := by rel [IH]
      _ = (k + 1 + 1) + k := by ring
      _ ≥ k + 1 + 1 := by norm_num

-- or

example (n : ℕ) : 2 ^ n ≥ n + 1 := by
  induction n with
  | zero => norm_num
  | succ k IH => omega


/- EXAMPLE 2
  Any positive rational number raised to a natural power is positive

  q ∈ ℚ and n ∈ ℕ with q > 0 → q^n > 0
-/
theorem rat_pow_pos (q : ℚ) (hq : 0 < q) (k : ℕ) : 0 < q ^ k := by
  induction k with
  | zero =>
    -- q ^ 0 = 1
    simp
  | succ k ih =>
    calc
      0 < q*q^k := mul_pos hq ih
      _ = q^(k+1) := by ring

-- or

theorem rat_pow_pos' (q : ℚ) (hq : 0 < q) (k : ℕ) : 0 < q ^ k := by
  induction k with
  | zero => simp
  | succ k ih => positivity

-- or

theorem rat_pow_pos'' (q : ℚ) (hq : 0 < q) (k : ℕ) : 0 < q ^ k := by
  positivity



theorem Bernoulli_inequality (a : ℝ) (ha : -1 ≤ a) (n : ℕ) : (1 + a) ^ n ≥ 1 + n * a := by
  induction n with
  | zero =>
    push_cast
    calc
      (1+a)^0 = 1 := by norm_num
      _ ≥ 1 := by norm_num
      _ = 1+0*a := by ring
  | succ k ih =>
    push_cast
    have ha2: 1+a ≥ 0 := by linarith
    have hk : (k:ℝ) ≥ 0 := by
      norm_cast
      apply Nat.zero_le k
    calc
        (1 + a)^(k+1) = (1 + a)*(1 + a)^k := by ring
        _ ≥ (1 + a)*(1 + k*a) := by rel [ih]
        _ = k * a^2 + (1 + (k + 1) * a) := by ring
        _ ≥ 1 + (k + 1) * a := by nlinarith



/- # INDUCTION FROM A STARTING POINT
  EXAMPLE 3
  We exemplify induction from a starting point
  using an example from Macbeth

  Show that: ∃ N : ℕ, ∀ n : ℕ, n ≥ N → 2 ^ n ≥ n ^ 2 + 4
-/


example : ∃ N : ℕ, ∀ n : ℕ, n ≥ N → 2 ^ n ≥ n ^ 2 + 4 := by
  use 5
  intro n h
  -- Induct directly on the `5 ≤ n` hypothesis
  induction h with
  | refl =>
    -- Base case: n = 5 (2^5 ≥ 5^2 + 4)
    norm_num
  | @step m hm ih =>
    -- hm : 5 ≤ m
    -- ih : 2 ^ m ≥ m ^ 2 + 4
    -- Goal : 2 ^ (m + 1) ≥ (m + 1) ^ 2 + 4
    -- Extract a 2 from the exponent so nlinarith can see `2 * 2^m`
    rw [pow_succ]
    -- nlinarith combines the IH (treated as X ≥ m^2 + 4)
    -- and the bound (m ≥ 5) to close the non-linear algebraic goal.
    nlinarith


example : ∃ N : ℕ, ∀ n : ℕ, n ≥ N → 2 ^ n ≥ n ^ 2 + 4 := by
  use 5
  intro n h
  -- Shifting the induction index
  obtain ⟨k, rfl⟩ : ∃ k, n = 5 + k := ⟨n - 5, by omega⟩
  induction k with
  | zero =>
    norm_num
  | succ k ih =>
    have h_exp : 2 ^ (5 + (k + 1)) = 2 ^ (5 + k) * 2 := by ring_nf
    rw [h_exp]
    have hk : 5 + k ≥ 5 := by omega
    nlinarith [ih hk]


example : ∃ N : ℕ, ∀ n : ℕ, n ≥ N → 2 ^ n ≥ n ^ 2 + 4 := by
  use 5
  intro n h
  obtain ⟨k, rfl⟩ : ∃ k, n = 5 + k := ⟨n - 5, by omega⟩
  induction k with
  | zero =>
    norm_num
  | succ k ih =>
    -- 1. Prove the trivial condition required by `ih`
    have hk : 5 + k ≥ 5 := by omega
    -- 2. Feed it into `ih` to remove the implication (→)
    specialize ih hk
    -- Now ih is exactly: 2 ^ (5 + k) ≥ (5 + k) ^ 2 + 4
    -- 3. Massage the exponent as before
    have h_exp : 2 ^ (5 + (k + 1)) = 2 ^ (5 + k) * 2 := by ring_nf
    rw [h_exp]
    -- 4. Now `nlinarith` can clearly see the pure inequality from `ih`
    nlinarith


/- EXERCISE 21
-/
example : ∃ N : ℕ, ∀ n : ℕ, n ≥ N → 3^n ≥ n^2 + 2*n + 5 := by
  use 3
  intro n hn
  induction' n, hn using Nat.le_induction with k hk ih
  · -- base case
    norm_num
  · -- inductive step
    have hk' : (2*k^2 +2*k+7) ≥ 0 := by apply Nat.zero_le
    calc
      3^(k+1) = 3 * 3^k := by ring
      _ ≥ 3 * (k^2 + 2*k + 5) := by rel [ih]
      _ = ((k + 1)^2 + 2*(k+1) + 5) + (2*k^2 +2*k+7):= by ring
      _ ≥ (k + 1)^2 + 2*(k+1) + 5 := le_add_of_nonneg_right hk'
