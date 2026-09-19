/-
Copyright (c) 2026 Iulian Simion. All rights reserved.
Released under the 3-Clause BSD License as described in the file LICENSE.
Authors: Iulian Simion, assisted by Claude (Anthropic) and Gemini (Google)
-/
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.GCongr

/-! # Solutions — Induction -/

-- 1
def sumOdd : ℕ → ℕ
  | 0 => 0
  | n + 1 => (2 * n + 1) + sumOdd n

theorem ex1 (n : ℕ) : sumOdd n = n ^ 2 :=
  by
    induction n with
    | zero => rfl
    | succ k ih =>
      show (2 * k + 1) + sumOdd k = (k + 1) ^ 2
      rw [ih]
      ring

-- 2
def v : ℕ → ℕ
  | 0 => 2
  | 1 => 4
  | n + 2 => v (n + 1) + 2 * v n

-- the values are 2, 4, 8, 16, 32, 64, so the closed form is `2 ^ (n + 1)`
theorem ex2 (n : ℕ) : v n = 2 ^ (n + 1) :=
  by
    induction n using Nat.twoStepInduction with
    | zero => rfl
    | one => rfl
    | more k ihk ihk1 =>
      -- ihk : v k = 2 ^ (k + 1),   ihk1 : v (k + 1) = 2 ^ (k + 2)
      show v (k + 1) + 2 * v k = 2 ^ (k + 3)
      rw [ihk, ihk1]
      ring

-- 3
theorem ex3 (n : ℕ) (hn : 0 < n) : ∃ k m, Odd m ∧ n = 2 ^ k * m :=
  by
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      rcases Nat.even_or_odd n with he | ho
      · -- the number `n` is even, so `n = j + j` with `j` half of it
        obtain ⟨j, hj⟩ := he
        have hj0 : 0 < j := by omega
        have hjlt : j < n := by omega
        obtain ⟨k, m, hm, hkm⟩ := ih j hjlt hj0
        refine ⟨k + 1, m, hm, ?_⟩
        rw [hj, hkm]
        ring
      · -- the number `n` is already odd, so no induction hypothesis is needed
        exact ⟨0, n, ho, by ring⟩
