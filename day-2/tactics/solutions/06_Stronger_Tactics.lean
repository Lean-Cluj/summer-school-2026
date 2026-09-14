/-
Copyright (c) 2026 Iulian Simion. All rights reserved.
Released under the 3-Clause BSD License as described in the file LICENSE.
Authors: Iulian Simion, assisted by Claude (Anthropic) and Gemini (Google)
-/
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Aesop

/-! # Solutions — Stronger tactics -/

-- 1
theorem ex1 (x y : ℕ) (h : y = 0) : x + y + 0 = x :=
  by simp [h]

-- 2
theorem ex2 (x y : ℝ) (h : y > 0) : x ^ 2 + y > 0 :=
  by nlinarith

-- 3
theorem ex3 (f : ℤ → ℤ) (x y : ℤ) (h1 : x = y) (h2 : f x ≠ f y) : False :=
  by grind
