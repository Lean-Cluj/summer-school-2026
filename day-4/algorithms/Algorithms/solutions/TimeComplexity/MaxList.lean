/-
Copyright (c) 2026 Iulian Simion. All rights reserved.
Released under the 3-Clause BSD License as described in the file LICENSE.
Authors: Iulian Simion, assisted by Claude (Anthropic) and Gemini (Google)
-/
import Algorithms.TimeComplexity.MaxList

/-! # Solutions — Counting steps: the maximum of a list -/

open Cslib.Algorithms.Lean

namespace MaxList.Solutions

-- 1
theorem maxListTM_ret (l : List ℕ) : (maxListTM l).ret = MaxList.maxList l := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    simp [maxListTM, MaxList.maxList, ih]

-- 2
theorem maxListTM'_time (l : List ℕ) : (maxListTM' l).time = l.length + 1 := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    simp [maxListTM', ih]

end MaxList.Solutions
