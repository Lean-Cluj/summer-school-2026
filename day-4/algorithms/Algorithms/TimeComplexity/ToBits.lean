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
import Algorithms.ToBits

open Cslib.Algorithms.Lean
open Asymptotics Filter

/-!
# Counting steps: binary representation

The function `toBitsTM` computes the binary digits of `n`, as `toBits` in
`ToBits.lean` of the first part does, with one tick for each digit. The
recursive call is on `n / 2`, so the number of steps is the number of binary
digits of `n`, which is `Nat.log2 n + 1` for `n ≥ 1`. The file proves that this
closed form is in `O(log n)`. Since it agrees with the cost for every `n ≥ 1`,
and therefore eventually, the cost is in `O(log n)` as well, by `IsBigO.congr'`,
as for `halvings` in `Asymptotics.lean`.

## Implementation

The definition distinguishes `n = 0` with `if n = 0`. For the proof of
termination, Lean adds the condition `¬ n = 0` of the second branch to the
context, and proves automatically from it that the recursive call is on a
smaller number, `n / 2 < n`.
-/

namespace ToBits

def toBitsTM (n : Nat) : TimeM Nat (List Bool) :=
  if n = 0 then
    pure []
  else do
    TimeM.tick 1
    let rest ← toBitsTM (n / 2)
    pure ((n % 2 == 1) :: rest)

#eval (toBitsTM 42).ret   -- [false, true, false, true, false, true]
#eval (toBitsTM 42).time  -- 6

/-!
## The cost as a function of the size of the input

The cost is `Nat.log2 n + 1` for every `n > 0`. The statement converts the
cost, a natural number, to a real number, since `toBitsTimeFunction` has real
values; the proof therefore moves between `ℕ` and `ℝ` with `exact_mod_cast`.

The proof is by strong induction, written as a recursive proof, as for
`fromBits_toBits`. After `unfold toBitsTM`, the tactic `split` separates the
case `n = 0`, which contradicts `hN` and is closed by `omega`. For `n ≥ 1`, the
tactic `rcases` distinguishes `n = 1`, which is computed directly, and `n ≥ 2`,
where the statement at `n / 2` is obtained by the recursive call and the
library lemma `Nat.log2_def` gives `Nat.log2 n = Nat.log2 (n / 2) + 1`.
-/

def toBitsTimeFunction (n : ℕ) : ℝ := Nat.log2 n + 1

theorem toBitsTimeFunction_correct (n : Nat) (hN : n > 0) :
    (toBitsTM n).time = toBitsTimeFunction n := by
  unfold toBitsTM
  split
  · omega
  · have h_one_le : 1 ≤ n := by omega
    rcases eq_or_lt_of_le h_one_le with rfl | hn_gt_one
    · -- the case `n = 1`
      unfold toBitsTM
      simp [toBitsTimeFunction]
    · -- the case `n ≥ 2`
      have h_half_pos : n / 2 > 0 := by omega
      have ih := toBitsTimeFunction_correct (n / 2) h_half_pos
      have h_log : (Nat.log2 n : ℝ) = (Nat.log2 (n / 2) : ℝ) + 1 := by
        have h_ge : 2 ≤ n := hn_gt_one
        have h_log_nat : Nat.log2 n = Nat.log2 (n / 2) + 1 := by
          rw [Nat.log2_def]
          simp [h_ge]
        exact_mod_cast h_log_nat
      simp [ih, toBitsTimeFunction, h_log]
      ring

/-!
## The complexity class

The function `toBitsTimeFunction` is the function `n ↦ Nat.log2 n + 1`, whose
bound is `Growth.log2_add_one_isBigO_logarithmic` in `Asymptotics.lean`. The
theorem below is proved by that term itself: when Lean checks its type, it
unfolds the definition of `toBitsTimeFunction`.
-/

theorem toBitsTimeFunction_isBigO_logarithmic : toBitsTimeFunction ∈ O(Growth.logarithmic) :=
  Growth.log2_add_one_isBigO_logarithmic

end ToBits
