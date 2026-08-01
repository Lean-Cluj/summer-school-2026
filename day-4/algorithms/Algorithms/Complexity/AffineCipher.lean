import Mathlib.Data.Vector.Basic
import Mathlib.Analysis.Asymptotics.Defs
import Cslib.Algorithms.Lean.TimeM
import Algorithms.Complexity.Asymptotics

open Cslib.Algorithms.Lean
open Asymptotics Filter


namespace EncryptionAlorithms

----------------------------------------------------------------------------------------------------
-- Affine Cipher implementation
----------------------------------------------------------------------------------------------------

def affineEncryptTM (msg : List UInt8) (a b : UInt8) : TimeM Nat (List UInt8) :=
  match msg with
  | [] => pure []
  | x :: xs => do
    TimeM.tick 1
    let rest ← affineEncryptTM xs a b
    pure ((x * a + b) :: rest)


----------------------------------------------------------------------------------------------------
-- Closed form of the time function for affineEncryptTM
----------------------------------------------------------------------------------------------------


def affineEncryptTimeFunction (n : ℕ) : ℝ := n


theorem affineEncryptTM_time (msg : List UInt8) (a b : UInt8) :
  (affineEncryptTM msg a b).time = msg.length := by
  induction msg with
  | nil => rfl
  | cons x xs ih =>
    calc
      (affineEncryptTM (x :: xs) a b).time
        = 1 + (affineEncryptTM xs a b).time := by rfl
      _ = 1 + xs.length                   := by rw [ih]
      _ = xs.length + 1                   := by omega
      _ = (x :: xs).length                := by rfl


----------------------------------------------------------------------------------------------------
-- Big-O formulation of the time complexity for affineEncryptTM
----------------------------------------------------------------------------------------------------


theorem affineEncryptTimeFunction_isBigO_linear : affineEncryptTimeFunction ∈ O(Growth.linear) := by
  apply isBigO_refl



end EncryptionAlorithms
