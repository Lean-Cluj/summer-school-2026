/-
Copyright (c) 2026 Iulian Simion. All rights reserved.
Released under the 3-Clause BSD License as described in the file LICENSE.
Authors: Iulian Simion, assisted by Claude (Anthropic) and Gemini (Google)
-/
import Algorithms.ToBits

/-! # Solutions — Binary representation -/

namespace ToBits.Solutions

-- 1
theorem toBits_two_mul_add_one (n : Nat) : toBits (2 * n + 1) = true :: toBits n := by
  rw [toBits]
  have h1 : (2 * n + 1) % 2 = 1 := by omega
  have h2 : (2 * n + 1) / 2 = n := by omega
  rw [h1, h2]
  rfl

-- 2
theorem fromBits_append_false (bs : List Bool) :
    fromBits (bs ++ [false]) = fromBits bs := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    cases b with
    | true =>
      change 1 + 2 * fromBits (bs ++ [false]) = 1 + 2 * fromBits bs
      rw [ih]
    | false =>
      change 2 * fromBits (bs ++ [false]) = 2 * fromBits bs
      rw [ih]

-- 3
-- The error: in the case `n + 1`, the digit and the recursive call are computed
-- from `n` instead of from `n + 1`. The corrected definition:
def toBits2 (n : Nat) : List Bool :=
  go n []
where
  go : Nat → List Bool → List Bool
    | 0, acc => acc.reverse
    | n + 1, acc => go ((n + 1) / 2) (((n + 1) % 2 == 1) :: acc)

#eval toBits2 4  -- [false, false, true]

theorem go_eq : (n : Nat) → (acc : List Bool) → toBits2.go n acc = acc.reverse ++ toBits n
  | 0, acc => by
    rw [toBits2.go, toBits, List.append_nil]
  | n + 1, acc => by
    rw [toBits2.go, go_eq ((n + 1) / 2), toBits]
    simp

theorem toBits2_eq (n : Nat) : toBits2 n = toBits n := by
  rw [toBits2, go_eq]
  rfl

end ToBits.Solutions
