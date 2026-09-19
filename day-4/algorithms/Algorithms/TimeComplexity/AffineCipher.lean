/-
Copyright (c) 2026 Iulian Simion. All rights reserved.
Released under the 3-Clause BSD License as described in the file LICENSE.
Authors: Iulian Simion, assisted by Claude (Anthropic) and Gemini (Google)
-/
import Mathlib.Analysis.Asymptotics.Defs
import Cslib.Algorithms.Lean.TimeM
import Algorithms.TimeComplexity.Asymptotics
import Algorithms.AffineCipher

open Cslib.Algorithms.Lean
open Asymptotics Filter

/-!
# Counting steps: the affine cipher

The function `affineEncryptTM` is `affineEncrypt` from `AffineCipher.lean` of
the first part, with the result type `TimeM ℕ (List UInt8)` and the cost model
of `xorCipherTM`: one step for each byte. As for the XOR cipher, the cost of a
message of length `n` is `n`, and `affineEncryptTimeFunction_correct` identifies
the cost with the function `affineEncryptTimeFunction`, which is in `O(n)`. The
results are given for completeness, with the proofs of
`TimeComplexity/XorCipher.lean`.

This file counts steps only. The function takes the bytes `a` and `b` as
separate arguments instead of a key of type `AffineKey`, and it ignores the
requirement that `a` has a multiplicative inverse, since the cost does not
depend on the key.
-/

namespace EncryptionAlgorithms

def affineEncryptTM (msg : List UInt8) (a b : UInt8) : TimeM ℕ (List UInt8) :=
  match msg with
  | [] => pure []
  | x :: xs => do
    TimeM.tick 1
    let rest ← affineEncryptTM xs a b
    pure ((x * a + b) :: rest)

#eval (affineEncryptTM [10, 20, 30] 3 42).ret   -- [72, 102, 132]
#eval (affineEncryptTM [10, 20, 30] 3 42).time  -- 3

/-! ## The cost as a function of the size of the input -/

def affineEncryptTimeFunction (n : ℕ) : ℝ := n

theorem affineEncryptTM_time (msg : List UInt8) (a b : UInt8) :
    (affineEncryptTM msg a b).time = msg.length := by
  induction msg with
  | nil => rfl
  | cons x xs ih =>
    calc
      (affineEncryptTM (x :: xs) a b).time
        = 1 + (affineEncryptTM xs a b).time := rfl
      _ = 1 + xs.length := by rw [ih]
      _ = xs.length + 1 := Nat.add_comm 1 xs.length
      _ = (x :: xs).length := rfl

theorem affineEncryptTimeFunction_correct (msg : List UInt8) (a b : UInt8) :
    ((affineEncryptTM msg a b).time : ℝ) = affineEncryptTimeFunction msg.length := by
  simp [affineEncryptTimeFunction, affineEncryptTM_time]

/-! ## The complexity class -/

theorem affineEncryptTimeFunction_isBigO_linear :
    affineEncryptTimeFunction ∈ O(Growth.linear) := by
  apply isBigO_refl

end EncryptionAlgorithms
