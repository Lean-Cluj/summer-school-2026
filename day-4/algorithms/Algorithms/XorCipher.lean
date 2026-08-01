import Std.Tactic.BVDecide


namespace EncryptionAlorithms


----------------------------------------------------------------------------------------------------
-- Byte-wise Xor Cipher implementation
----------------------------------------------------------------------------------------------------


def xorCipher (msg : List UInt8) (key : UInt8) : List UInt8 :=
  match msg with
  | [] => []
  | b :: bs => (b ^^^ key) :: xorCipher bs key


----------------------------------------------------------------------------------------------------
-- Concrete Examples
----------------------------------------------------------------------------------------------------


#eval xorCipher ([] : List UInt8) 42
-- Output: []

#eval xorCipher [(10 : UInt8)] 5
-- Output: [15]

#eval xorCipher [(0 : UInt8), 255, 170] 255
-- Output: [255, 0, 85]

#eval xorCipher [(104 : UInt8), 101, 108, 108, 111] 42
-- Output: [66, 79, 70, 70, 69]

#eval xorCipher (xorCipher [(104 : UInt8), 101, 108, 108, 111] 42) 42
-- Output: [104, 101, 108, 108, 111]


----------------------------------------------------------------------------------------------------
-- Formal Verification
----------------------------------------------------------------------------------------------------


theorem xor_inv (b key : UInt8) : b ^^^ key ^^^ key = b := by
  bv_decide


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


end EncryptionAlorithms
