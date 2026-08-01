import Mathlib.Algebra.Group.Nat.Defs

namespace FastExp

----------------------------------------------------------------------------------------------------
-- Fast exponentiation
----------------------------------------------------------------------------------------------------


def fastExp (x : Nat) (bits : List Bool) : Nat :=
  match bits with
  | [] => 1
  | b :: bs =>
    let rest := fastExp (x * x) bs
    if b then
      x * rest
    else
      rest

----------------------------------------------------------------------------------------------------
-- Concrete Examples
----------------------------------------------------------------------------------------------------

#eval fastExp 5 []
-- Output: 1

#eval fastExp 5 [true]
-- Output: 5

#eval fastExp 3 [false, true]
-- Output: 9

#eval fastExp 2 [true, true]
-- Output: 8

#eval fastExp 2 [false, false, true]
-- Output: 16

#eval fastExp 2 [false, true, false, true]
-- Output: 1024

#eval fastExp 0 [true, true]
-- Output: 0


----------------------------------------------------------------------------------------------------
-- Formal Verification
----------------------------------------------------------------------------------------------------


def toNat : List Bool → Nat
  | [] => 0
  | true :: bs => 1 + 2 * toNat bs
  | false :: bs => 2 * toNat bs


theorem fastExp_correct (x : Nat) (bits : List Bool) :
    fastExp x bits = x ^ (toNat bits) := by
  induction bits generalizing x with
  | nil => rfl
  | cons b bs ih =>
    have hpow : (x * x) ^ toNat bs = x ^ (2 * toNat bs) := by
      rw [← pow_two, pow_mul]
    cases b with
    | true =>
      change x * fastExp (x * x) bs = x ^ (1 + 2 * toNat bs)
      rw [ih (x * x), hpow, pow_add, pow_one]
    | false =>
      change fastExp (x * x) bs = x ^ (2 * toNat bs)
      rw [ih (x * x), hpow]


end FastExp
