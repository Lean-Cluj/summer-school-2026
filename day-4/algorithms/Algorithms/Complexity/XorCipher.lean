import Mathlib.Data.Vector.Basic
import Mathlib.Analysis.Asymptotics.Defs
import Cslib.Algorithms.Lean.TimeM
import Algorithms.Complexity.Asymptotics

open Cslib.Algorithms.Lean
open Asymptotics Filter

namespace EncryptionAlorithms

----------------------------------------------------------------------------------------------------
-- Byte-wise Xor Cipher implementation
----------------------------------------------------------------------------------------------------


def xorCipherTM (msg : List UInt8) (key : UInt8) : TimeM Nat (List UInt8) :=
  match msg with
  | [] => pure []
  | b :: bs => do
    TimeM.tick 1 -- Note: You can also use CSLib's syntactic sugar `✓` here instead
    let rest ← xorCipherTM bs key
    pure ((b ^^^ key) :: rest)


----------------------------------------------------------------------------------------------------
-- Closed form of the time function for xorCipherTM
----------------------------------------------------------------------------------------------------


def xorCipherTimeFunction (n : ℕ) : ℝ := n


theorem xorCipherTM_time (msg : List UInt8) (key : UInt8) :
  (xorCipherTM msg key).time = msg.length := by
  induction msg with
  | nil => rfl
  | cons b bs ih =>
    calc
      (xorCipherTM (b :: bs) key).time
        = 1 + (xorCipherTM bs key).time := by rfl
      _ = 1 + bs.length               := by rw [ih]
      _ = bs.length + 1               := by omega
      _ = (b :: bs).length            := by rfl


----------------------------------------------------------------------------------------------------
-- Big-O formulation of the time complexity for xorCipherTM
----------------------------------------------------------------------------------------------------


theorem xorCipherTimeFunction_isBigO_linear : xorCipherTimeFunction ∈ O(Growth.linear) := by
  apply isBigO_refl


end EncryptionAlorithms
