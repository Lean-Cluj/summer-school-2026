/-
Copyright (c) 2026 Iulian Simion. All rights reserved.
Released under the 3-Clause BSD License as described in the file LICENSE.
Authors: Iulian Simion, assisted by Claude (Anthropic) and Gemini (Google)
-/
import Mathlib.Tactic.Linarith

/-! # Solutions — Implication and the universal quantifier -/

-- 1
theorem ex1 (p q r : Prop) : (p → q) → (q → r) → (p → r) :=
  by
    intro hpq hqr hp
    exact hqr (hpq hp)

-- 2
theorem ex2 : ∀ n : Nat, n + 0 = n :=
  fun _ => rfl

-- 3
theorem ex3 (h : ∀ n : Nat, n ≤ n + 1) : 5 ≤ 6 :=
  h 5
