/-
Copyright (c) 2026 Iulian Simion. All rights reserved.
Released under the 3-Clause BSD License as described in the file LICENSE.
Authors: Iulian Simion, assisted by Claude (Anthropic) and Gemini (Google)
-/
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push

/-! # Solutions — The existential quantifier, and negation -/

-- 1
-- The tactic `use` supplies the witness; its small discharger does not settle
-- `101 > 100`, so one more tactic is needed.
theorem ex1 : ∃ n : Nat, n > 100 :=
  by
    use 101
    norm_num

-- 2
theorem ex2 (h : ∃ n : Nat, n > 5) : ∃ n : Nat, n > 3 :=
  by
    obtain ⟨a, ha⟩ := h
    exact ⟨a, by linarith⟩

-- 3
theorem ex3 : ¬∃ n : Nat, n + 1 = 0 :=
  by
    push Not
    intro n
    omega
