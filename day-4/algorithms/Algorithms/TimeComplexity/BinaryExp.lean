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
import Algorithms.TimeComplexity.ToBits
import Algorithms.BinaryExp

open Cslib.Algorithms.Lean
open Asymptotics Filter
open ToBits

/-!
# Counting steps: exponentiation by squaring

The function `fastExpTM` is `fastExp` from `BinaryExp.lean` of the first part,
with the result type `TimeM ℕ ℕ` in place of `ℕ` and with one tick for each
binary digit of the exponent. The cost therefore counts digits, not
multiplications: each digit costs one squaring and at most one further
multiplication, so the number of multiplications is at most twice the cost. A
constant factor does not change the class in `O(·)`.

The cost for a list of digits is its length. For an exponent `N`, the digits
are the result of `toBitsTM N`, and the number of digits is the cost of
`toBitsTM N`, which is in `O(log N)` by `TimeComplexity/ToBits.lean`. The cost
of `fastExpTM` is therefore in `O(log N)`.
-/

namespace FastExp

def fastExpTM (x : Nat) (bits : List Bool) : TimeM Nat Nat :=
  match bits with
  | [] => pure 1
  | b :: bs => do
    TimeM.tick 1
    let rest ← fastExpTM (x * x) bs
    if b then
      pure (x * rest)
    else
      pure rest

#eval (fastExpTM 3 (toBits 13)).ret   -- 1594323
#eval (fastExpTM 3 (toBits 13)).time  -- 4

/-!
## The cost as a function of the exponent

The function `fastExpTimeFunction x N` is the cost of `fastExpTM` for the base
`x` and the digits of `N`. Its closed form, `Nat.log2 N + 1` for `N > 0`, is
proved in two steps.

1. The cost of `fastExpTM x bits` is `bits.length`, by induction on `bits`.
2. The list `(toBitsTM n).ret` has as many elements as `toBitsTM n` has ticks,
   by the same recursion as `toBitsTM`.

With the cost `Nat.log2 N + 1` of `toBitsTM N` from
`TimeComplexity/ToBits.lean`, this gives the closed form.
-/

def fastExpTimeFunction (x : Nat) (N : Nat) : ℝ :=
  ((fastExpTM x (toBitsTM N).ret).time : ℝ)

theorem fastExpTM_time_eq_length (x : Nat) (bits : List Bool) :
    (fastExpTM x bits).time = bits.length := by
  induction bits generalizing x with
  | nil => rfl
  | cons b bs ih =>
    simp only [fastExpTM, TimeM.time_bind, TimeM.time_tick, ih, List.length_cons]
    split <;> simp <;> omega

theorem toBitsTM_ret_length_eq_time (n : Nat) :
    (toBitsTM n).ret.length = (toBitsTM n).time := by
  unfold toBitsTM
  split
  · rfl
  · have ih := toBitsTM_ret_length_eq_time (n / 2)
    simp [ih]
    omega

theorem fastExpTimeFunction_eq (x N : Nat) (hN : 0 < N) :
    fastExpTimeFunction x N = Nat.log2 N + 1 := by
  unfold fastExpTimeFunction
  rw [fastExpTM_time_eq_length x (toBitsTM N).ret, toBitsTM_ret_length_eq_time N]
  exact toBitsTimeFunction_correct N hN

/-!
## The complexity class

By the closed form, `fastExpTimeFunction x N` equals `toBitsTimeFunction N` for
every `N > 0`, and therefore for all sufficiently large `N`. The lemma
`IsBigO.congr'` then transfers the bound of `toBitsTimeFunction`.
-/

theorem fastExpTimeFunction_isBigO_logarithmic (x : Nat) :
    fastExpTimeFunction x ∈ O(Growth.logarithmic) := by
  have h_eq : ∀ᶠ N in atTop, toBitsTimeFunction N = fastExpTimeFunction x N := by
    filter_upwards [eventually_gt_atTop 0] with N hN
    exact (fastExpTimeFunction_eq x N hN).symm
  exact toBitsTimeFunction_isBigO_logarithmic.congr' h_eq (EventuallyEq.refl _ _)

/-!
The line `filter_upwards [eventually_gt_atTop 0] with N hN` in the proof of
`h_eq` works as follows. Write `P N` for the equation of the two functions at
`N`, and `Q N` for `0 < N`.

* Goal before the line: `∀ᶠ N in atTop, P N`.
* Fact supplied in the brackets: `eventually_gt_atTop 0 : ∀ᶠ N in atTop, Q N`.
* Principle, the library lemma `Filter.Eventually.mono`:
  from `∀ᶠ N in atTop, Q N` and `∀ N, Q N → P N`, conclude
  `∀ᶠ N in atTop, P N`.
* So `filter_upwards` replaces the goal by `∀ N, Q N → P N`.
* `with N hN` introduces `N : ℕ` and `hN : Q N`, that is, `hN : 0 < N`.
* Goal after the line: `P N`.
-/

end FastExp
