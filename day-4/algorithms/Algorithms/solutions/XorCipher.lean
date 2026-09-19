/-
Copyright (c) 2026 Iulian Simion. All rights reserved.
Released under the 3-Clause BSD License as described in the file LICENSE.
Authors: Iulian Simion, assisted by Claude (Anthropic) and Gemini (Google)
-/
import Algorithms.XorCipher

/-! # Solutions — The XOR cipher -/

namespace EncryptionAlgorithms.Solutions

-- 1
theorem xorCipher_zero (msg : List UInt8) : xorCipher msg 0 = msg := by
  have h (b : UInt8) : b ^^^ 0 = b := by bv_decide
  induction msg with
  | nil => rfl
  | cons b bs ih =>
    change (b ^^^ 0) :: xorCipher bs 0 = b :: bs
    rw [h, ih]

-- 2
theorem length_xorCipher (msg : List UInt8) (key : UInt8) :
    (xorCipher msg key).length = msg.length := by
  induction msg with
  | nil => rfl
  | cons b bs ih =>
    change (xorCipher bs key).length + 1 = bs.length + 1
    rw [ih]

-- 3
theorem xorCipher_xorCipher (msg : List UInt8) (k₁ k₂ : UInt8) :
    xorCipher (xorCipher msg k₁) k₂ = xorCipher msg (k₁ ^^^ k₂) := by
  have h (b : UInt8) : b ^^^ k₁ ^^^ k₂ = b ^^^ (k₁ ^^^ k₂) := by bv_decide
  induction msg with
  | nil => rfl
  | cons b bs ih =>
    change (b ^^^ k₁ ^^^ k₂) :: xorCipher (xorCipher bs k₁) k₂
      = (b ^^^ (k₁ ^^^ k₂)) :: xorCipher bs (k₁ ^^^ k₂)
    rw [h, ih]

end EncryptionAlgorithms.Solutions
