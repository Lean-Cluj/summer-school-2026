/-
Copyright (c) 2026 Iulian Simion. All rights reserved.
Released under the 3-Clause BSD License as described in the file LICENSE.
Authors: Iulian Simion, assisted by Claude (Anthropic) and Gemini (Google)
-/
import Mathlib.Data.Nat.Basic

/-!
# Binary representation

Every natural number `n` has a **binary representation**

  `n = b₀ + 2 * b₁ + 4 * b₂ + ⋯ + 2 ^ (k - 1) * b_(k-1)`

with digits `bᵢ` in `{0, 1}`, and it is unique when the last digit
`b_(k-1)` is required to be `1`. The number `0` is represented by no digits.
The first digit `b₀` is `n % 2`, and the remaining digits are the digits of
`n / 2`, since `n = n % 2 + 2 * (n / 2)`.

Here a representation is a list of Booleans with the least significant digit
first, `true` for the digit `1` and `false` for `0`. The number `6 = 0 + 2 + 4`
is represented by `[false, true, true]`.

## Implementation

The expression `a == b` compares two values with the comparison of the type
class `BEq` and evaluates to a Boolean, `true` or `false`. The expression
`a = b`, in contrast, is a proposition, which is proved rather than evaluated.
For natural numbers, `(a == b) = true` holds exactly when `a = b`.
-/

#eval 5 % 2 == 1   -- true
#eval 4 % 2 == 1   -- false
#check 5 % 2 == 1  -- 5 % 2 == 1 : Bool
#check 5 % 2 = 1   -- 5 % 2 = 1 : Prop

/-!
The function `toBits` computes the representation, and it computes each digit
as a Boolean with `==`. The function `fromBits` computes the number that a list
of digits represents.
-/

namespace ToBits

def toBits : Nat → List Bool
  | 0 => []
  | n + 1 => ((n + 1) % 2 == 1) :: toBits ((n + 1) / 2)

def fromBits : List Bool → Nat
  | [] => 0
  | true :: bs => 1 + 2 * fromBits bs
  | false :: bs => 2 * fromBits bs

/-!
## Termination

The recursion of `toBits` is not structural: its recursive call is on
`(n + 1) / 2`, which does not occur in the pattern `n + 1`. Lean accepts the
definition because it proves automatically that `(n + 1) / 2 < n + 1`. The
evaluation therefore terminates, since a strictly decreasing sequence of natural
numbers is finite. A relation with this property is called **well-founded**, and
the definition is a definition by **well-founded recursion**.

For such a definition, Lean does not store the two lines of the definition as
they are. It builds the function `toBits` from them and from the proof that the
argument decreases, and then proves the two lines as theorems: `toBits 0 = []`
and `toBits (n + 1) = ((n + 1) % 2 == 1) :: toBits ((n + 1) / 2)`.
Lean marks every definition by well-founded recursion as **irreducible**: it
does not unfold the definition when it checks a proof by `rfl` or `decide`. This
affects only proofs. The command `#eval` runs code compiled from the definition
as written, and in a proof the tactics `rw [toBits]` and `simp [toBits]` rewrite
with the two theorems, `rw` one step at a time and `simp` repeatedly.
-/

#eval toBits 4  -- [false, false, true]

-- example : toBits 4 = [false, false, true] := rfl
--   ⇒ error: Type mismatch: `rfl` has type `?m = ?m`
--     but is expected to have type `toBits 4 = [false, false, true]`

example : toBits 4 = [false, false, true] := by simp [toBits]

/-! ## Tests -/

#eval toBits 0                                -- []
#eval fromBits []                             -- 0
#eval fromBits [false, true, false, true]     -- 10
#eval toBits 42                               -- [false, true, false, true, false, true]
#eval fromBits (toBits 42)                    -- 42
#eval toBits (fromBits [true, true, false, true])  -- [true, true, false, true]

/-!
## Specification

A full specification of `toBits` states that `toBits n` is the binary
representation of `n` from the introduction: its digits satisfy
`n = b₀ + 2 * b₁ + ⋯ + 2 ^ (k - 1) * b_(k-1)`, and its last digit is not
`false`. Since the representation is unique, these two properties determine the
list. The function `fromBits` computes the sum on the right, as
`b₀ + 2 * (b₁ + 2 * (⋯))`, so the first property reads
`fromBits (toBits n) = n`. As for the ciphers, the specification proved here is
restricted to this property: converting a number to its digits and back returns
the number.

The proof below is itself defined by recursion on `n`, like `toBits`. It is a
proof by strong induction: the statement for a number may be proved from the
statement for any smaller number, not only for its predecessor. In the case
`n + 1`, the recursive call `fromBits_toBits ((n + 1) / 2)` gives the induction
hypothesis `ih`, the statement for `(n + 1) / 2`, and Lean checks termination as
it did for `toBits`.

The case `n + 1` splits on the first digit: `(n + 1) % 2` is `0` or `1`. In each
case, `rw [hb]` replaces the Boolean comparison by its value, `unfold fromBits`
applies the matching equation of `fromBits`, `rw [ih]` replaces
`fromBits (toBits ((n + 1) / 2))` by `(n + 1) / 2`, and `omega` proves the
remaining equation of natural numbers.
-/

theorem fromBits_toBits : (n : Nat) → fromBits (toBits n) = n
  | 0 => by
    rw [toBits, fromBits]
  | n + 1 => by
    rw [toBits]
    have ih := fromBits_toBits ((n + 1) / 2)
    have h_mod : (n + 1) % 2 = 0 ∨ (n + 1) % 2 = 1 := by omega
    rcases h_mod with hm0 | hm1
    · have hb : ((n + 1) % 2 == 1) = false := by simp [hm0]
      rw [hb]
      unfold fromBits
      rw [ih]
      omega
    · have hb : ((n + 1) % 2 == 1) = true := by simp [hm1]
      rw [hb]
      unfold fromBits
      rw [ih]
      omega

/-!
The converse, `toBits (fromBits bs) = bs`, fails: a list ending in `false` is
not the representation that `toBits` produces. Exercise 2 shows that such
digits do not change the value.

## Other implementations

The two implementations below are intended to compute the same list as
`toBits`: `toBits2` collects the digits in an extra argument, and `toBits3`
computes the first digit with `if`. The evaluations show that both differ from
`toBits`, and exercise 3 asks for the error.

### The function `toBits2`

The function `toBits2` calls an auxiliary function `go`, which collects the
digits in an extra argument `acc`, the **accumulator**, and reverses it when the
number reaches `0`.
-/

def toBits2 (n : Nat) : List Bool :=
  go n []
where
  go : Nat → List Bool → List Bool
    | 0, acc => acc.reverse
    | n + 1, acc => go (n / 2) ((n % 2 == 1) :: acc)

#eval toBits 4   -- [false, false, true]
#eval toBits2 4  -- [true, false]

/-!
### The function `toBits3`

The function `toBits3` distinguishes the number `0` with `if` instead of a
pattern, computes the first digit, and calls `toBits2` for the remaining digits.
-/

def toBits3 (n : Nat) : List Bool :=
  if n = 0 then []
  else (n % 2 == 1) :: toBits2 (n / 2)

#eval toBits3 4  -- [false, true]

/-!
### Lean core and Mathlib

The Lean core library defines `Nat.testBit n i`, the digit `bᵢ` of `n` as a
Boolean, and `Nat.toDigits b n`, the list of the digits of `n` in base `b` as
characters, with the most significant digit first. Mathlib defines `Nat.bits`,
which returns the same list as `toBits`, and `Nat.digits b n`, the list of the
digits of `n` in base `b` as natural numbers, with the least significant digit
first. Its function `Nat.ofDigits` computes the number from such a list, as
`fromBits` does for base `2`.
-/

#eval Nat.testBit 6 0   -- false
#eval Nat.testBit 6 1   -- true
#eval Nat.toDigits 2 6  -- ['1', '1', '0']

/-!
## Exercises

Solutions: `solutions/ToBits.lean`.
-/

/-! ### 1
Prove that the representation of an odd number `2 * n + 1` is `true` followed by
the representation of `n`.

Hint: `rw [toBits]`, then compute `(2 * n + 1) % 2` and `(2 * n + 1) / 2` with
`omega`. -/

theorem toBits_two_mul_add_one (n : Nat) : toBits (2 * n + 1) = true :: toBits n := sorry

/-! ### 2
Prove that appending the digit `false` does not change the value of a list of
digits. -/

theorem fromBits_append_false (bs : List Bool) :
    fromBits (bs ++ [false]) = fromBits bs := sorry

/-! ### 3
Find the error in the definition of `toBits2.go` and correct it. Then prove that
the corrected `toBits2` agrees with `toBits`; the correction also corrects
`toBits3`.

Hint: prove the more general statement
`toBits2.go n acc = acc.reverse ++ toBits n` for every list `acc` first, by
recursion on `n` as in `fromBits_toBits`. -/

theorem toBits2_eq (n : Nat) : toBits2 n = toBits n := sorry

end ToBits
