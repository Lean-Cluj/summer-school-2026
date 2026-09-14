/-
Copyright (c) 2026 Iulian Simion. All rights reserved.
Released under the 3-Clause BSD License as described in the file LICENSE.
Authors: Iulian Simion, assisted by Claude (Anthropic) and Gemini (Google)
-/
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-! # Solutions — Conjunction, disjunction, equivalence -/

-- 1
theorem ex1 (n : Nat) (h : n = 4) : n > 3 ∧ n < 5 :=
  by
    constructor
    · linarith
    · linarith

-- 2
theorem ex2 (p q r : Prop) (hpr : p → r) (hqr : q → r) : p ∨ q → r :=
  by
    intro h
    obtain hp | hq := h
    · exact hpr hp
    · exact hqr hq

-- 3
theorem ex3 (p q : Prop) (h : p ↔ q) (hq : q) : p :=
  h.mpr hq
