import Mathlib.Data.Vector.Basic
import Mathlib.Analysis.Asymptotics.Defs
import Cslib.Algorithms.Lean.TimeM
import Algorithms.Complexity.Asymptotics

open Cslib.Algorithms.Lean
open Asymptotics Filter

namespace MaxVect


----------------------------------------------------------------------------------------------------
-- Maximum element in a vector using TimeM
----------------------------------------------------------------------------------------------------


def maxVectTM : {n : ℕ} → List.Vector ℕ n → TimeM ℕ ℕ
  | 0,     _ => pure 0
  | _ + 1, v => do
      let m ← maxVectTM v.tail
      ✓
      pure (max v.head m)


----------------------------------------------------------------------------------------------------
-- Closed form of the time function for maxVectTM
----------------------------------------------------------------------------------------------------


def maxVectTimeFunction (n : ℕ) : ℝ := n

theorem maxVectTimeFunction_correct {n : ℕ} :
  ∀ v : List.Vector Nat n,
  ((maxVectTM v).time : ℝ) = maxVectTimeFunction n :=
  by
    intro v
    induction n with
    | zero =>
      simp [maxVectTM, maxVectTimeFunction]
    | succ n ih =>
      simp [maxVectTM, maxVectTimeFunction, ih]


----------------------------------------------------------------------------------------------------
-- Big-O formulation of the time complexity for maxVectTM
----------------------------------------------------------------------------------------------------


theorem maxVectTimeFunction_isBigO_linear : maxVectTimeFunction ∈ O(Growth.linear) := by
  apply isBigO_refl

end MaxVect
