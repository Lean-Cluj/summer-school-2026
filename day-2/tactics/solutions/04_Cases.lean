/-
Copyright (c) 2026 Iulian Simion. All rights reserved.
Released under the 3-Clause BSD License as described in the file LICENSE.
Authors: Iulian Simion, assisted by Claude (Anthropic) and Gemini (Google)
-/
import Mathlib

/-! # Solutions — Case analysis -/

-- 1
theorem ex1 (b : Bool) : (!b) = true ∨ (!b) = false :=
  by
    cases b with
    | true => right; rfl
    | false => left; rfl

-- 2
theorem ex2 (n : ℕ) : n = 0 ∨ ∃ k, n = k + 1 :=
  by
    cases n with
    | zero => left; rfl
    | succ k => right; exact ⟨k, rfl⟩

-- 3
theorem ex3 (n : Fin 4) : n.val * n.val ≤ 9 :=
  by fin_cases n <;> norm_num
