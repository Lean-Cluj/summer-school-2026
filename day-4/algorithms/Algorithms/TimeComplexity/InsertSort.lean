/-
Copyright (c) 2026 Iulian Simion. All rights reserved.
Released under the 3-Clause BSD License as described in the file LICENSE.
Authors: Iulian Simion, assisted by Claude (Anthropic) and Gemini (Google)
-/
import Cslib.Algorithms.Lean.TimeM
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Log
import Algorithms.TimeComplexity.Asymptotics
import Algorithms.InsertSort

open Cslib.Algorithms.Lean
open Asymptotics Filter

/-!
# Counting steps: insertion sort

The functions `insertTM` and `insertSortTM` are `insert` and `insertSort` from
`InsertSort.lean` of the first part, with the result type `TimeM ℕ (List ℕ)`.
The cost model charges one tick for each comparison `x ≤ y`.

Inserting into a list of length `n` performs at most `n` comparisons, one for
each element of the list; it performs fewer when it stops at the first element
`y` with `x ≤ y`. Insertion sort on a list of length `n` inserts into sorted
lists of lengths `0, 1, …, n - 1`, so it performs at most
`0 + 1 + ⋯ + (n - 1) = n * (n - 1) / 2` comparisons, which is at most `n ^ 2`.

Unlike the cost of the algorithms in the previous files, the cost of insertion
sort depends on the order of the elements, not only on the length of the list.
The theorems below are therefore upper bounds, as are those of the next file,
`TimeComplexity/BinarySearchTree.lean`.

## Implementation
-/

namespace SortingAlgorithms

def insertTM (x : Nat) : List Nat → TimeM Nat (List Nat)
  | [] => pure [x]
  | y :: ys => do
      ✓                                  -- compare x ≤ y
      if x ≤ y then pure (x :: y :: ys)
      else do
        let zs ← insertTM x ys
        pure (y :: zs)

def insertSortTM : List Nat → TimeM Nat (List Nat)
  | [] => pure []
  | x :: xs => do
      let ys ← insertSortTM xs
      insertTM x ys

#eval (insertSortTM [1, 2, 3, 4, 5]).time  -- 4
#eval (insertSortTM [5, 4, 3, 2, 1]).time  -- 10

/-!
## The length of the results

The bound for `insertSortTM` applies the bound for `insertTM` to the list
returned by the recursive call, so it needs the length of that list. Both
lemmas are proved by induction. In the step, `have step : … := by rfl` records
the unfolded form of the definition. In the proof for `insertTM`, `split` then
distinguishes the two branches of the `if`.
-/

theorem insertTM_ret_length (x : Nat) (l : List Nat) :
    (insertTM x l).ret.length = l.length + 1 := by
  induction l with
  | nil => rfl
  | cons y ys ih =>
    have step : (insertTM x (y :: ys)).ret =
        (if x ≤ y then pure (x :: y :: ys)
          else do let zs ← insertTM x ys; pure (y :: zs)).ret := by rfl
    rw [step]
    split
    · rfl
    · have h2 : ((do let zs ← insertTM x ys; pure (y :: zs)) : TimeM Nat (List Nat)).ret =
          y :: (insertTM x ys).ret := by rfl
      rw [h2]
      simp [ih]

theorem insertSortTM_ret_length (l : List Nat) :
    (insertSortTM l).ret.length = l.length := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    have step : (insertSortTM (x :: xs)).ret =
        (insertTM x (insertSortTM xs).ret).ret := by rfl
    rw [step, insertTM_ret_length, ih]
    rfl

/-!
## The bounds

The cost of `insertTM x (y :: ys)` is `1` for the comparison plus, in the second
branch, the cost of the recursive call. The cost of `insertSortTM (x :: xs)` is
the cost of sorting `xs` plus the cost of inserting `x` into the result, a list
of length `xs.length`. The equations proved by `rfl` hold because `pure` costs
`0` and `>>=` adds the costs, as the lemmas `TimeM.time_pure` and
`TimeM.time_bind` of `TimeComplexity/MaxList.lean` state. In the last step,
`linarith` adds `ih` and `h2`, which bound the cost by `k ^ 2 + k` for
`k = xs.length`, and compares the result with `(k + 1) ^ 2`, which it expands to
`k ^ 2 + 2 * k + 1`.
-/

theorem insertTM_time_le (x : Nat) (l : List Nat) :
    (insertTM x l).time ≤ l.length := by
  induction l with
  | nil => rfl
  | cons y ys ih =>
    have h1 : (insertTM x (y :: ys)).time =
        1 + (if x ≤ y then pure (x :: y :: ys)
          else do let zs ← insertTM x ys; pure (y :: zs)).time := by rfl
    rw [h1]
    split
    · exact Nat.le_add_left 1 ys.length
    · have h2 : ((do let zs ← insertTM x ys; pure (y :: zs)) : TimeM Nat (List Nat)).time =
          (insertTM x ys).time := by rfl
      rw [h2]
      have h3 : (y :: ys).length = ys.length + 1 := by rfl
      rw [h3]
      omega

theorem insertSortTM_time_le (l : List Nat) :
    (insertSortTM l).time ≤ l.length ^ 2 := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    have h1 : (insertSortTM (x :: xs)).time =
        (insertSortTM xs).time + (insertTM x (insertSortTM xs).ret).time := by rfl
    rw [h1]
    have h2 : (insertTM x (insertSortTM xs).ret).time ≤ (insertSortTM xs).ret.length :=
      insertTM_time_le x (insertSortTM xs).ret
    rw [insertSortTM_ret_length] at h2
    have h3 : (x :: xs).length = xs.length + 1 := by rfl
    rw [h3]
    linarith

/-!
## The bound as a function of the size of the input

The function `insertSortTimeFunctionBound n` is `n ^ 2`, and it bounds the cost
of `insertSortTM` on every list of length `n`. On a list in decreasing order,
each insertion runs to the end of the list, and the cost is
`0 + 1 + ⋯ + (n - 1) = n * (n - 1) / 2`: for `n = 5`, the second test above
gives `10`, while the bound is `25`. The bound is therefore not attained, but
its order of growth is, since `n * (n - 1) / 2` is not in `O(n)`.
-/

def insertSortTimeFunctionBound (n : ℕ) : ℝ := (n : ℝ) ^ 2

theorem insertSortTimeFunctionBound_correct (l : List Nat) :
    ((insertSortTM l).time : ℝ) ≤ insertSortTimeFunctionBound l.length := by
  simp only [insertSortTimeFunctionBound]
  exact_mod_cast insertSortTM_time_le l

/-!
## The complexity class

The function `insertSortTimeFunctionBound` is equal to `Growth.quadratic` by
definition, so `isBigO_refl` proves that the bound is in `O(n ^ 2)`. The cost
itself is a function of the list, not of a number, so `O(·)` does not apply to
it directly. It applies to the largest cost among the lists of length `n`, the
**worst-case cost**, which is at most `insertSortTimeFunctionBound n` by the
previous theorem and is therefore also in `O(n ^ 2)`.
-/

theorem insertSortTimeFunctionBound_isBigO_quadratic :
    insertSortTimeFunctionBound ∈ O(Growth.quadratic) := by
  apply isBigO_refl

end SortingAlgorithms
