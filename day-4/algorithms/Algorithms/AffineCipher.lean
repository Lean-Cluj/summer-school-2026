import Std.Tactic.BVDecide

namespace EncryptionAlorithms

----------------------------------------------------------------------------------------------------
-- Affine Cipher implementation
----------------------------------------------------------------------------------------------------


structure AffineKey where
  a : UInt8
  b : UInt8
  a_inv : UInt8
  inv_proof : a * a_inv = 1

def affineEncrypt (msg : List UInt8) (k : AffineKey) : List UInt8 :=
  match msg with
  | [] => []
  | x :: xs => (x * k.a + k.b) :: affineEncrypt xs k

def affineDecrypt (msg : List UInt8) (k : AffineKey) : List UInt8 :=
  match msg with
  | [] => []
  | y :: ys => (((y - k.b) * k.a_inv)) :: affineDecrypt ys k


----------------------------------------------------------------------------------------------------
-- Concrete Examples
----------------------------------------------------------------------------------------------------


def myKey : AffineKey := {
  a := 3
  b := 42
  a_inv := 171
  inv_proof := by decide
}

def myMessage : List UInt8 := [10, 20, 30]


#eval affineEncrypt myMessage myKey -- Outputs: [72, 102, 132]

#eval affineDecrypt [72, 102, 132] myKey -- Outputs: [10, 20, 30]


-- Unit tests
example : affineEncrypt myMessage myKey = [72, 102, 132] := by rfl

example : affineDecrypt [72, 102, 132] myKey = myMessage := by rfl


----------------------------------------------------------------------------------------------------
-- Formal Verification
----------------------------------------------------------------------------------------------------


theorem affine_inv (x : UInt8) (k : AffineKey) :
  (x * k.a + k.b - k.b) * k.a_inv = x := by
  have h := k.inv_proof
  bv_decide


theorem affineCipher_correct (msg : List UInt8) (k : AffineKey) :
  affineDecrypt (affineEncrypt msg k) k = msg := by
  induction msg with
  | nil => rfl
  | cons x xs ih =>
    calc
      affineDecrypt (affineEncrypt (x :: xs) k) k
        = affineDecrypt ((x * k.a + k.b) :: affineEncrypt xs k) k := by rfl
      _ = (((x * k.a + k.b) - k.b) * k.a_inv) :: affineDecrypt (affineEncrypt xs k) k := by rfl
      _ = x :: affineDecrypt (affineEncrypt xs k) k := by rw [affine_inv x k]
      _ = x :: xs := by rw [ih]
