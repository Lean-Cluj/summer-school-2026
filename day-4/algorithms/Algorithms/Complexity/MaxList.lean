import Mathlib.Analysis.Asymptotics.Defs
import Cslib.Algorithms.Lean.TimeM
import Algorithms.Complexity.Asymptotics

open Cslib.Algorithms.Lean
open Asymptotics Filter

namespace MaxList


----------------------------------------------------------------------------------------------------
-- Maximum element in a list using TimeM
----------------------------------------------------------------------------------------------------


def maxListTM : List ℕ → TimeM ℕ ℕ
  | []      => pure 0
  | x :: xs => do
      let m ← maxListTM xs
      ✓
      pure (max x m)


----------------------------------------------------------------------------------------------------
-- Closed form of the time function for maxListTM
----------------------------------------------------------------------------------------------------


def maxListTimeFunction (n : ℕ) : ℝ := n

theorem maxListTimeFunction_correct :
  ∀ l : List ℕ,
  ((maxListTM l).time : ℝ) = maxListTimeFunction l.length :=
  by
    intro l
    induction l with
    | nil =>
      simp [maxListTM, maxListTimeFunction]
    | cons x xs ih =>
      simp [maxListTM, maxListTimeFunction, ih]


----------------------------------------------------------------------------------------------------
-- Big-O formulation of the time complexity for maxListTM
----------------------------------------------------------------------------------------------------


theorem maxListTimeFunction_isBigO_linear : maxListTimeFunction ∈ O(Growth.linear) := by
  apply isBigO_refl

end MaxList
