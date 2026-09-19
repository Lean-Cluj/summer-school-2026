/-
Copyright (c) 2026 Iulian Simion. All rights reserved.
Released under the 3-Clause BSD License as described in the file LICENSE.
Authors: Iulian Simion, assisted by Claude (Anthropic) and Gemini (Google)
-/
import Algorithms.AffineCipher

/-! # Solutions — The affine cipher -/

namespace EncryptionAlgorithms.Solutions

-- 1
theorem affineEncrypt_affineDecrypt (msg : List UInt8) (k : AffineKey) :
    affineEncrypt (affineDecrypt msg k) k = msg := by
  have hinv (y : UInt8) : (y - k.b) * k.a_inv * k.a + k.b = y := by
    have h := k.inv_proof
    bv_decide
  induction msg with
  | nil => rfl
  | cons y ys ih =>
    change ((y - k.b) * k.a_inv * k.a + k.b) :: affineEncrypt (affineDecrypt ys k) k = y :: ys
    rw [hinv, ih]

-- 2
-- An even byte times any byte is even modulo 256, so it cannot be `1`.
theorem key_a_odd (k : AffineKey) : k.a % 2 = 1 := by
  have h := k.inv_proof
  bv_decide

-- 3
-- `5 * 205 = 1025 = 4 * 256 + 1`
theorem exists_inv_five : ∃ c : UInt8, 5 * c = 1 := ⟨205, by decide⟩

end EncryptionAlgorithms.Solutions
