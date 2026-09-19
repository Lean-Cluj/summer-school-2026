/-
Copyright (c) 2026 Iulian Simion. All rights reserved.
Released under the 3-Clause BSD License as described in the file LICENSE.
Authors: Iulian Simion, assisted by Claude (Anthropic) and Gemini (Google)
-/
import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.Tactic.Ring
import Algorithms.ToBits

/-!
# Exponentiation by squaring

Computing `x ^ n` by repeated multiplication, `x * x * ⋯ * x`, takes `n - 1`
multiplications for `n ≥ 1`. **Exponentiation by squaring** uses the binary
representation of `n` from `ToBits.lean` and takes far fewer.

Write `n = b₀ + 2 * m`, where `b₀ = n % 2` is the first digit and `m = n / 2`.
Then

  `x ^ n = x ^ b₀ * x ^ (2 * m) = x ^ b₀ * (x * x) ^ m`.

The factor `x ^ b₀` is `x` if `b₀ = 1` and `1` if `b₀ = 0`, and `(x * x) ^ m` is
computed in the same way from the digits of `m`, which are the remaining digits
of `n`. Each digit costs one squaring `x * x` and at most one further
multiplication, so the number of multiplications is at most twice the number of
binary digits of `n`. A number `n ≥ 1` has `⌊log₂ n⌋ + 1` binary digits.

## Implementation

The function `fastExp` receives the digits of the exponent as a list of
Booleans, least significant digit first, as produced by `toBits`.
-/

namespace FastExp

open ToBits

def fastExp (x : Nat) (bits : List Bool) : Nat :=
  match bits with
  | [] => 1
  | b :: bs =>
    let rest := fastExp (x * x) bs
    if b then
      x * rest
    else
      rest

/-!
The keyword `let` gives the name `rest` to the result of the recursive call,
which both branches of the `if` use.

The expression `if c then t else e` is notation for `ite c t e`. The function
`ite` takes a decidable proposition `c` and returns `t` if `c` holds and `e`
otherwise. The condition `b` of `fastExp` is a Boolean, so Lean replaces it by
the proposition `b = true`.

Being provable and being decidable are different properties of a proposition.
Decidability is modeled by the inductive type `Decidable p`. A value of
`Decidable p` is either `isFalse h`, with a proof `h : ¬ p`, or `isTrue h`, with
a proof `h : p`, and `ite` returns `e` or `t` according to which of the two it
is.
-/

#check @ite  -- {α : Sort u_1} → (c : Prop) → [h : Decidable c] → α → α → α
#print Decidable

/-! ## Tests -/

#eval fastExp 5 []                            -- 1
#eval fastExp 5 [true]                        -- 5
#eval fastExp 3 [false, true]                 -- 9
#eval fastExp 2 [true, true]                  -- 8
#eval fastExp 2 [false, false, true]          -- 16
#eval fastExp 2 [false, true, false, true]    -- 1024
#eval fastExp 0 [true, true]                  -- 0
#eval fastExp 3 (toBits 13)                   -- 1594323

/-!
## Specification

The result is `x` raised to the number that the digits represent:
`fastExp x bits = x ^ fromBits bits`.

The proof is by structural induction on the list `bits`, following the
recursion of `fastExp`. The recursive call of `fastExp` is on the base `x * x`,
not on `x`, so the step needs the statement for `bs` with the base `x * x`.

With `induction bits`, the variable `x` stays fixed during the induction, and
in the step the hypothesis is `ih : fastExp x bs = x ^ fromBits bs`, for this
`x` only. After `fastExp` is unfolded, the goal contains `fastExp (x * x) bs`,
which `ih` does not mention, so `rw [ih]` fails. With
`induction bits generalizing x`, the statement proved by induction is
`∀ x, fastExp x bits = x ^ fromBits bits`. In the step, the hypothesis is
`ih : ∀ x, fastExp x bs = x ^ fromBits bs`, and `ih (x * x)` is its instance
for the base `x * x`.
-/

theorem fastExp_correct (x : Nat) (bits : List Bool) :
    fastExp x bits = x ^ fromBits bits := by
  induction bits generalizing x with
  | nil => rfl
  | cons b bs ih =>
    have hpow : (x * x) ^ fromBits bs = x ^ (2 * fromBits bs) := by
      rw [← pow_two, pow_mul]
    cases b with
    | true =>
      change x * fastExp (x * x) bs = x ^ (1 + 2 * fromBits bs)
      rw [ih (x * x), hpow, pow_add, pow_one]
    | false =>
      change fastExp (x * x) bs = x ^ (2 * fromBits bs)
      rw [ih (x * x), hpow]

/-!
The equation `hpow` follows from the library lemmas `pow_two` and `pow_mul`. In
each case of `b`, the tactic `change` replaces the target by the form it takes
when `fastExp` and `fromBits` are unfolded and the `if` is evaluated, as in
`MaxList.lean`.

Combined with `fromBits_toBits`, the specification gives the correctness of the
complete algorithm: converting `n` to binary and running `fastExp` computes
`x ^ n`.
-/

theorem fastExp_toBits (x n : Nat) : fastExp x (toBits n) = x ^ n := by
  rw [fastExp_correct, fromBits_toBits]

/-!
## Exercises

Solutions: `solutions/BinaryExp.lean`.
-/

/-! ### 1
The function `powNaive` computes a power by repeated multiplication. Prove that it
computes `x ^ n`.

Hint: induction on `n`, and the library lemma `pow_succ x n : x ^ (n + 1) =
x ^ n * x`. -/

def powNaive (x : Nat) : Nat → Nat
  | 0 => 1
  | n + 1 => powNaive x n * x

theorem powNaive_eq (x n : Nat) : powNaive x n = x ^ n := sorry

/-! ### 2
Prove that `fastExp 1 bits = 1` for every list of digits. -/

theorem fastExp_one (bits : List Bool) : fastExp 1 bits = 1 := sorry

/-! ### 3
Prove that `fastExp` is multiplicative in the base. Do not use
`fastExp_correct`: use induction on `bits`, generalizing both `x` and `y`.

Hint: in the step, the bases of the recursive calls are `x * y * (x * y)`,
`x * x` and `y * y`. The tactic `ring` proves the equations of natural numbers
that are needed. -/

theorem fastExp_mul (x y : Nat) (bits : List Bool) :
    fastExp (x * y) bits = fastExp x bits * fastExp y bits := sorry

end FastExp
