/-
Copyright (c) 2026 Iulian Simion. All rights reserved.
Released under the 3-Clause BSD License as described in the file LICENSE.
Authors: Iulian Simion, assisted by Claude (Anthropic) and Gemini (Google)
-/
import Mathlib.Data.Vector.Basic
import Mathlib.Analysis.Asymptotics.Defs
import Cslib.Algorithms.Lean.TimeM
import Algorithms.TimeComplexity.Asymptotics
import Algorithms.MaxVect

open Cslib.Algorithms.Lean
open Asymptotics Filter

/-!
# Counting steps: the maximum of a vector

The function `maxVectTM` is `maxVect` from `MaxVect.lean` of the first part,
with the result type `TimeM ℕ ℕ` and the cost model of `maxListTM`: one tick for
each comparison. As for `maxList`, the cost of a vector of length `n` is `n`, so
it is in `O(n)`. The proofs follow those of `TimeComplexity/MaxList.lean` and
are given for completeness. The difference is that the induction is on the
length `n`, which is part of the type, as in `MaxVect.lean` of the first part.
-/

namespace MaxVect

def maxVectTM : {n : ℕ} → List.Vector ℕ n → TimeM ℕ ℕ
  | 0, _ => pure 0
  | _ + 1, v => do
      let m ← maxVectTM v.tail
      ✓
      pure (max v.head m)

#eval (maxVectTM ⟨[4, 12, 3, 8], rfl⟩).time  -- 4

/-! ## The cost as a function of the size of the input -/

def maxVectTimeFunction (n : ℕ) : ℝ := n

theorem maxVectTimeFunction_correct {n : ℕ} :
    ∀ v : List.Vector ℕ n, ((maxVectTM v).time : ℝ) = maxVectTimeFunction n := by
  intro v
  induction n with
  | zero =>
    simp [maxVectTM, maxVectTimeFunction]
  | succ n ih =>
    simp [maxVectTM, maxVectTimeFunction, ih]

/-! ## The complexity class -/

theorem maxVectTimeFunction_isBigO_linear : maxVectTimeFunction ∈ O(Growth.linear) := by
  apply isBigO_refl

end MaxVect
