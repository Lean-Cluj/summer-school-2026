/-
Copyright (c) 2026 Iulian Simion. All rights reserved.
Released under the 3-Clause BSD License as described in the file LICENSE.
Authors: Iulian Simion, assisted by Claude (Anthropic) and Gemini (Google)
-/
import Std.Tactic.BVDecide

/-!
# The affine cipher

An **affine cipher** encrypts each symbol `x` of a message, viewed as a number
modulo `m`, as `a x + b` modulo `m`, and its key consists of `a` and `b`. The
same construction for blocks of `n` symbols, with an `n × n` matrix `A` in
place of `a` and a vector `b`, is called the **affine Hill cipher**.

The affine cipher in this file encrypts bytes, so `m = 256`. It encrypts a byte
`x` as `x * a + b`, with the arithmetic of `UInt8`, and its key consists of the
two bytes `a` and `b`.

Decryption undoes the two operations in the reverse order: it subtracts `b`,
and then multiplies by a byte `a⁻¹` with `a * a⁻¹ = 1` modulo 256, called a
**multiplicative inverse** of `a` modulo 256. Then

  `(x * a + b - b) * a⁻¹ = x * (a * a⁻¹) = x * 1 = x`.

A multiplicative inverse of `a` modulo 256 exists exactly when `a` and 256 have
no common divisor greater than `1`, that is, when `a` is odd. For `a = 3`, the
inverse is `171`, since `3 * 171 = 513 = 2 * 256 + 1`.

## A key contains a proof

The key of a cipher is the data that encryption and decryption need besides the
message. The key of the affine cipher consists of the bytes `a` and `b`.
Decryption also needs the inverse `a⁻¹`, which is determined by `a`. The key in
this file stores `a⁻¹` as well, so that decryption does not have to compute it.

The file models the key as a **structure**: an inductive type with a single
constructor, whose arguments are called the **fields** of the structure. The
structure `AffineKey` has four fields: the bytes `a`, `b` and `a_inv`, where
`a_inv` stands for `a⁻¹`, and `inv_proof`, whose type is the proposition
`a * a_inv = 1`. Since the constructor takes a proof of this equation as an
argument, every key satisfies it. For each field, Lean defines a function that
returns it, written `k.a` for a key `k`, and a key can be written with the
names of its fields, as `myKey` below.
-/

namespace EncryptionAlgorithms

structure AffineKey where
  a : UInt8
  b : UInt8
  a_inv : UInt8
  inv_proof : a * a_inv = 1

#print AffineKey  -- the four fields and the constructor `AffineKey.mk`

def affineEncrypt (msg : List UInt8) (k : AffineKey) : List UInt8 :=
  match msg with
  | [] => []
  | x :: xs => (x * k.a + k.b) :: affineEncrypt xs k

def affineDecrypt (msg : List UInt8) (k : AffineKey) : List UInt8 :=
  match msg with
  | [] => []
  | y :: ys => ((y - k.b) * k.a_inv) :: affineDecrypt ys k

/-!
## Tests

In the key below, the tactic `decide` proves `3 * 171 = 1` by evaluating the
product in `UInt8`.
-/

def myKey : AffineKey := {
  a := 3
  b := 42
  a_inv := 171
  inv_proof := by decide
}

def myMessage : List UInt8 := [10, 20, 30]

#eval affineEncrypt myMessage myKey       -- [72, 102, 132]
#eval affineDecrypt [72, 102, 132] myKey  -- [10, 20, 30]

/-!
The first byte `10` of the message is encrypted as `10 * 3 + 42 = 72`.
Decryption computes `(72 - 42) * 171 = 5130`, which is `10` modulo 256, since
`5130 = 20 * 256 + 10`.
-/

#eval (10 : UInt8) * 3 + 42        -- 72
#eval ((72 : UInt8) - 42) * 171    -- 10

/-!
A test can also be written as an `example` proved by `rfl`. Lean then checks
the equation each time the file is compiled, and reports an error if it fails.
-/

example : affineEncrypt myMessage myKey = [72, 102, 132] := by rfl

example : affineDecrypt [72, 102, 132] myKey = myMessage := by rfl

/-!
## Specification

As for the XOR cipher, the specification considered here is only the round-trip
property: decrypting the encryption of a message with the same key returns the
message.

The round-trip property for a single byte is the identity of the introduction.
It is proved by `bv_decide`, as for the XOR cipher. The identity holds only
because `a * a_inv = 1`, and the tactic `bv_decide` uses the hypothesis `h` in
the context as an assumption about the bits. The line `have h := k.inv_proof`
makes this hypothesis visible; `bv_decide` would also find it without this line,
since it splits the structure `k` into its fields.
-/

theorem affine_inv (x : UInt8) (k : AffineKey) :
    (x * k.a + k.b - k.b) * k.a_inv = x := by
  have h := k.inv_proof
  bv_decide

/-!
The round-trip property for messages has the same proof as
`xorCipher_involutive`.
-/

theorem affineCipher_correct (msg : List UInt8) (k : AffineKey) :
    affineDecrypt (affineEncrypt msg k) k = msg := by
  induction msg with
  | nil => rfl
  | cons x xs ih =>
    calc
      affineDecrypt (affineEncrypt (x :: xs) k) k
        = affineDecrypt ((x * k.a + k.b) :: affineEncrypt xs k) k := by rfl
      _ = ((x * k.a + k.b - k.b) * k.a_inv) :: affineDecrypt (affineEncrypt xs k) k := by rfl
      _ = x :: affineDecrypt (affineEncrypt xs k) k := by rw [affine_inv x k]
      _ = x :: xs := by rw [ih]

/-!
## Exercises

Solutions: `solutions/AffineCipher.lean`.
-/

/-! ### 1
Prove the round-trip property in the other order: encrypting a decrypted
message returns the message.

Hint: prove the identity for a single byte with `bv_decide` first. It needs
`a_inv * a = 1`, which `bv_decide` derives from `k.inv_proof`. -/

theorem affineEncrypt_affineDecrypt (msg : List UInt8) (k : AffineKey) :
    affineEncrypt (affineDecrypt msg k) k = msg := sorry

/-! ### 2
Prove that the multiplier `a` of every key is odd. -/

theorem key_a_odd (k : AffineKey) : k.a % 2 = 1 := sorry

/-! ### 3
Find a multiplicative inverse of `5` modulo 256, and prove that it is one.

Hint: the tactic `exists c` gives `c` as the witness of `∃ c, P c` and then
tries to prove `P c` automatically, which succeeds here. -/

theorem exists_inv_five : ∃ c : UInt8, 5 * c = 1 := sorry

end EncryptionAlgorithms
