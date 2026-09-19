/-
Copyright (c) 2026 Iulian Simion. All rights reserved.
Released under the 3-Clause BSD License as described in the file LICENSE.
Authors: Iulian Simion, assisted by Claude (Anthropic) and Gemini (Google)
-/
import Std.Tactic.BVDecide

/-!
# The XOR cipher

In general, a **symmetric cipher** consists of two functions. The encryption
function turns a message and a key into a ciphertext, and the decryption
function turns the ciphertext and the same key back into the message. The most
basic requirement in the specification of a cipher is its **correctness**, also
called the **round-trip property**: decrypting the encryption of a message with
the same key returns the message. The security of a cipher is outside the
scope of these notes.

The XOR cipher in this file encrypts a message, which is a list of bytes, with a
key consisting of a single byte. Its encryption and decryption functions are the
same function. The type `UInt8` of bytes has the 256 values `0, 1, …, 255`, each
stored in 8 bits. Its operations `+`, `-` and `*` are computed modulo 256, while
`/` and `%` are division and remainder as for natural numbers.

## Exclusive or

The **exclusive or** of two bits is `1` when exactly one of them is `1`, and `0`
otherwise. For two bytes, the operation `^^^` computes the exclusive or of the
bits in each of the 8 positions. For example, `10` is `00001010` in binary and
`5` is `00000101`, so `10 ^^^ 5` is `00001111`, which is `15`.

The function `Nat.toDigits 2` gives the binary digits of a natural number,
without the leading zeros of a byte. In the evaluations below, the annotation
`(10 : UInt8)` sets the type of the numerals to `UInt8`; without it, their type
is `Nat`. The prefix `0b` writes a number in binary.
-/

#eval Nat.toDigits 2 10                      -- ['1', '0', '1', '0']
#eval (10 : UInt8) ^^^ 5                     -- 15
#eval (0b00001010 : UInt8) ^^^ 0b00000101    -- 15
#eval (10 : UInt8) ^^^ 10                    -- 0
#eval (10 : UInt8) ^^^ 0                     -- 10

/-!
The operation is associative, and every byte `k` satisfies `k ^^^ k = 0` and
`k ^^^ 0 = k`. Therefore every byte `b` satisfies

  `(b ^^^ k) ^^^ k = b ^^^ (k ^^^ k) = b ^^^ 0 = b`.

## Implementation

The XOR cipher implemented here combines each byte of the message with the
one-byte key by `^^^`.
By the identity above, applying the cipher twice with the same key returns the
message, so the same function serves for encryption and for decryption.
-/

namespace EncryptionAlgorithms

def xorCipher (msg : List UInt8) (key : UInt8) : List UInt8 :=
  match msg with
  | [] => []
  | b :: bs => (b ^^^ key) :: xorCipher bs key

/-! ## Tests -/

#eval xorCipher [] 42                                               -- []
#eval xorCipher [10] 5                                               -- [15]
#eval xorCipher [0, 255, 170] 255                                    -- [255, 0, 85]
#eval xorCipher [104, 101, 108, 108, 111] 42                         -- [66, 79, 70, 70, 69]
#eval xorCipher (xorCipher [104, 101, 108, 108, 111] 42) 42          -- [104, 101, 108, 108, 111]

/-!
## Specification

The identity for a single byte is proved by the tactic `bv_decide`. It applies
to statements about `Bool`, about `BitVec w` for a fixed width `w`, and about
the integer types of fixed width: `UInt8`, …, `UInt64`, `USize`, `Int8`, …,
`Int64` and `ISize`. It also splits structures whose fields have these types.
The tactic translates the negation of the statement into a formula about the
individual bits and passes it to a SAT solver. When the solver finds that the
formula has no solution, it returns a certificate, a record of the reasoning
that shows that there is no solution. Compiled code checks the certificate, and the result of this check is added as an
axiom, which the kernel accepts without checking it again. The proof therefore
also relies on the correctness of the Lean compiler.

The operation `^^^` associates to the left, so `b ^^^ key ^^^ key` is
`(b ^^^ key) ^^^ key`.
-/

theorem xor_inv (b key : UInt8) : b ^^^ key ^^^ key = b := by
  bv_decide

/-!
The last axiom in the list below, whose name contains `bv_decide`, is the result
of the check. The list also contains `Classical.choice`, which the proof obtains
from the library lemmas that `bv_decide` uses.
-/

#print axioms xor_inv
-- [propext, Classical.choice, Quot.sound, an axiom named `…bv_decide…`]

/-!
This identity does not need a SAT solver. Lean core proves the three facts used
above as `UInt8.xor_assoc`, `UInt8.xor_self` and `UInt8.xor_zero`, and a proof
by `rw` with them depends only on `propext` and `Quot.sound`. The tactic
`bv_decide` is useful for statements about bits for which no such lemmas are
available.

The round-trip property for messages follows by induction on the message.
-/

theorem xorCipher_involutive (msg : List UInt8) (key : UInt8) :
    xorCipher (xorCipher msg key) key = msg := by
  induction msg with
  | nil =>
    rfl
  | cons b bs ih =>
    calc
      xorCipher (xorCipher (b :: bs) key) key
        = xorCipher ((b ^^^ key) :: xorCipher bs key) key := by rfl
      _ = (b ^^^ key ^^^ key) :: xorCipher (xorCipher bs key) key := by rfl
      _ = b :: xorCipher (xorCipher bs key) key := by rw [xor_inv b key]
      _ = b :: bs := by rw [ih]

/-!
In the `calc` chain, the first two steps unfold the definition of `xorCipher`,
so `rfl` proves them. The third step applies `xor_inv` to the first byte, and
the fourth applies the induction hypothesis to the rest of the message.
-/

/-!
## Exercises

Solutions: `solutions/XorCipher.lean`.
-/

/-! ### 1
Prove that the key `0` leaves every message unchanged.

Hint: prove `b ^^^ 0 = b` with `bv_decide` first, then use induction on the
message. -/

theorem xorCipher_zero (msg : List UInt8) : xorCipher msg 0 = msg := sorry

/-! ### 2
Prove that the cipher preserves the length of the message. -/

theorem length_xorCipher (msg : List UInt8) (key : UInt8) :
    (xorCipher msg key).length = msg.length := sorry

/-! ### 3
Prove that encrypting with `k₁` and then with `k₂` is the same as encrypting once
with `k₁ ^^^ k₂`. -/

theorem xorCipher_xorCipher (msg : List UInt8) (k₁ k₂ : UInt8) :
    xorCipher (xorCipher msg k₁) k₂ = xorCipher msg (k₁ ^^^ k₂) := sorry

end EncryptionAlgorithms
