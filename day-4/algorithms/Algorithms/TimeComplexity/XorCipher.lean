/-
Copyright (c) 2026 Iulian Simion. All rights reserved.
Released under the 3-Clause BSD License as described in the file LICENSE.
Authors: Iulian Simion, assisted by Claude (Anthropic) and Gemini (Google)
-/
import Mathlib.Analysis.Asymptotics.Defs
import Cslib.Algorithms.Lean.TimeM
import Algorithms.TimeComplexity.Asymptotics
import Algorithms.XorCipher

open Cslib.Algorithms.Lean
open Asymptotics Filter

/-!
# Counting steps: the XOR cipher

The function `xorCipherTM` is `xorCipher` from `XorCipher.lean` of the first
part, with the result type `TimeM ℕ (List UInt8)`. Its cost model charges one
step for each byte of the message, with the step `TimeM.tick 1`, which the
notation `✓` of CSLib also runs. As for `maxList`, the cost of a message of
length `n` is `n`, and `xorCipherTimeFunction_correct` identifies the cost with
the function `xorCipherTimeFunction`, which is in `O(n)`. The results are given
for completeness. Unlike in `TimeComplexity/MaxList.lean`, the proof of the cost
is a `calc` chain instead of `simp`: its first step evaluates the `do` block,
which `rfl` proves, and the other steps apply the induction hypothesis and
rearrange the sum.
-/

namespace EncryptionAlgorithms

def xorCipherTM (msg : List UInt8) (key : UInt8) : TimeM ℕ (List UInt8) :=
  match msg with
  | [] => pure []
  | b :: bs => do
    TimeM.tick 1
    let rest ← xorCipherTM bs key
    pure ((b ^^^ key) :: rest)

#eval (xorCipherTM [104, 101, 108, 108, 111] 42).time  -- 5

/-! ## The cost as a function of the size of the input -/

def xorCipherTimeFunction (n : ℕ) : ℝ := n

theorem xorCipherTM_time (msg : List UInt8) (key : UInt8) :
    (xorCipherTM msg key).time = msg.length := by
  induction msg with
  | nil => rfl
  | cons b bs ih =>
    calc
      (xorCipherTM (b :: bs) key).time
        = 1 + (xorCipherTM bs key).time := rfl
      _ = 1 + bs.length := by rw [ih]
      _ = bs.length + 1 := Nat.add_comm 1 bs.length
      _ = (b :: bs).length := rfl

theorem xorCipherTimeFunction_correct (msg : List UInt8) (key : UInt8) :
    ((xorCipherTM msg key).time : ℝ) = xorCipherTimeFunction msg.length := by
  simp [xorCipherTimeFunction, xorCipherTM_time]

/-! ## The complexity class -/

theorem xorCipherTimeFunction_isBigO_linear : xorCipherTimeFunction ∈ O(Growth.linear) := by
  apply isBigO_refl

end EncryptionAlgorithms
