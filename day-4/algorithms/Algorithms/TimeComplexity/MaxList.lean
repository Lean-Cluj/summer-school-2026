/-
Copyright (c) 2026 Iulian Simion. All rights reserved.
Released under the 3-Clause BSD License as described in the file LICENSE.
Authors: Iulian Simion, assisted by Claude (Anthropic) and Gemini (Google)
-/
import Mathlib.Analysis.Asymptotics.Defs
import Cslib.Algorithms.Lean.TimeM
import Algorithms.TimeComplexity.Asymptotics
import Algorithms.MaxList

open Cslib.Algorithms.Lean
open Asymptotics Filter

/-!
# Counting steps: the maximum of a list

This file and the other files of the folder `TimeComplexity`, except
`Asymptotics.lean`, return to the algorithms of the first part. Each file
writes an algorithm with a result of type `TimeM ℕ α`, which carries, besides
the result, a count of the steps that the program itself declares. It then
proves a closed form or an upper bound of this count, and states its growth
class in the notation `O(·)` of `Asymptotics.lean`.

## The type `TimeM`

A statement about running time needs a precise count of steps. The library
CSLib provides the type `TimeM T α`, where `T` is the type of the cost; the
files of this folder take `T = ℕ`. A term `c : TimeM ℕ α` is a structure with
two fields: the value `c.ret : α`, the result of a computation, and the natural
number `c.time`, its **cost**.

An algorithm with result type `TimeM ℕ α` is written in Lean's `do` notation,
which is built from the operations `pure` and `>>=`. CSLib defines both for
`TimeM ℕ`, and makes it an instance of the type class `Monad`, which collects
them. A `do` block is a sequence of steps, and the function
`maxListTM` below uses three kinds of step. Each kind has a fixed rule for the
result and the cost of the computation:

* `pure a` turns a value `a : α` into a computation of type `TimeM ℕ α` that
  performs no steps: its result is `a` and its cost is `0`;
* `let x ← c` followed by `rest` runs `c`, names its result `x`, and continues
  with `rest`; the cost is the cost of `c` plus the cost of `rest`;
* `✓ rest` adds `1` to the cost of `rest`, and does not change its result.

The simp lemmas `TimeM.time_pure`, `TimeM.time_bind` and `TimeM.time_tick`
state these rules for the cost, and `TimeM.ret_pure`, `TimeM.ret_bind` and
`TimeM.ret_tick` state them for the result. In their statements, `m >>= f` is
the form of `let x ← m` followed by `f x`, and `TimeM.tick c` is the
computation with result `()` and cost `c`. The step `✓ rest` runs `TimeM.tick 1`
and then `rest`.
-/

#check TimeM.time_pure  -- (pure a).time = 0
#check TimeM.time_bind  -- (m >>= f).time = m.time + (f m.ret).time
#check TimeM.time_tick  -- (TimeM.tick c).time = c
#check TimeM.ret_pure   -- (pure a).ret = a
#check TimeM.ret_bind   -- (m >>= f).ret = (f m.ret).ret
#check TimeM.ret_tick   -- (TimeM.tick c).ret = ()

/-!
The cost counts the ticks written into the program and nothing else. The
choice of the operations that receive a tick is the **cost model**, and a
statement about the cost holds for that cost model. In `maxListTM` below, the
branch for `x :: xs` has one tick and performs one comparison, `max x m`, and
the branch for `[]` has neither, so the cost is the number of comparisons.

## Implementation

The function `maxListTM` is `maxList` from `MaxList.lean` of the first part,
with the result type `TimeM ℕ ℕ` in place of `ℕ`. Exercise 1 proves that its
result is `maxList l`.
-/

namespace MaxList

def maxListTM : List ℕ → TimeM ℕ ℕ
  | [] => pure 0
  | x :: xs => do
      let m ← maxListTM xs
      ✓
      pure (max x m)

#eval (maxListTM [4, 12, 3, 8]).ret   -- 12
#eval (maxListTM [4, 12, 3, 8]).time  -- 4

/-!
## The cost as a function of the size of the input

The cost of `maxListTM l` depends only on the length of `l`: it is
`l.length`. The function `maxListTimeFunction` gives the cost for each length
`n`, and the theorem below proves that it is correct. The function is given by
a formula without recursion, a **closed form**. Its values are real numbers, as
for the functions of `Asymptotics.lean`, so the theorem converts the cost, a
natural number, to a real number.

In the step of the induction, `simp` computes the cost of the `do` block with
the lemmas for `TimeM` and rewrites the cost of the recursive call with the
induction hypothesis.
-/

def maxListTimeFunction (n : ℕ) : ℝ := n

theorem maxListTimeFunction_correct :
    ∀ l : List ℕ, ((maxListTM l).time : ℝ) = maxListTimeFunction l.length := by
  intro l
  induction l with
  | nil =>
    simp [maxListTM, maxListTimeFunction]
  | cons x xs ih =>
    simp [maxListTM, maxListTimeFunction, ih]

/-!
## The complexity class

The function `maxListTimeFunction` is equal to `Growth.linear` by definition,
so `isBigO_refl` proves that it is in `O(n)`. Since
`maxListTimeFunction_correct` identifies this function with the cost, the cost
is in `O(n)`: the cost equals a closed form, and the closed form is in `O(n)`.
-/

theorem maxListTimeFunction_isBigO_linear : maxListTimeFunction ∈ O(Growth.linear) := by
  apply isBigO_refl

/-!
## Exercises

Solutions: `solutions/TimeComplexity/MaxList.lean`.
-/

/-! ### 1
Prove that `maxListTM` computes `maxList`.

Hint: induction on `l`, and `simp` with the definitions of `maxListTM` and
`MaxList.maxList` and the induction hypothesis. -/

theorem maxListTM_ret (l : List ℕ) : (maxListTM l).ret = MaxList.maxList l := sorry

/-! ### 2
In the cost model of `maxListTM'`, the empty list also costs one step. Prove
the closed form of its cost. -/

def maxListTM' : List ℕ → TimeM ℕ ℕ
  | [] => do
      ✓
      pure 0
  | x :: xs => do
      let m ← maxListTM' xs
      ✓
      pure (max x m)

theorem maxListTM'_time (l : List ℕ) : (maxListTM' l).time = l.length + 1 := sorry

end MaxList
