/-
Copyright (c) 2026 Iulian Simion. All rights reserved.
Released under the 3-Clause BSD License as described in the file LICENSE.
Authors: Iulian Simion, assisted by Claude (Anthropic) and Gemini (Google)
-/
import Mathlib.Tactic.NormNum
import Mathlib.Data.Real.Basic

/-!
# `Prop` and `Bool`

This file distinguishes the type `Prop` of propositions from the type `Bool` of
truth values, introduces `Decidable` as the connection between them, and
compares three proofs of `2 + 2 = 4`: by `rfl`, by `decide` and by `norm_num`.

* The data type `Bool` has exactly two terms, `true` and `false`. It is what
  a programming language calls a boolean: something a program computes and
  branches on.
* The terms of the type `Prop` are the propositions. A term of a proposition is
  a *proof* of it, and a proposition may be true without anything having
  computed that fact.
-/

#check Bool
#check true
#check false

#check Prop
#check True
#check False

/-!
The term `true : Bool` is a value; `True : Prop` is a proposition. Likewise
`false : Bool` and `False : Prop`. They are different terms of different
types.

## How a `Bool` becomes a proposition

Lean will accept a `Bool` where a proposition is expected, by inserting a
coercion: `b : Bool` becomes the proposition `b = true`.

The `#check` below shows the result: what looks like the value `true` used as a
proposition is really the equation `true = true`.
-/

#check (true : Prop)

section
variable (b : Bool)

-- a boolean `b` used as a proposition means `b = true`
example : (b : Prop) = (b = true) := rfl

end

/-!
As far as truth goes, the two readings agree: `(true : Prop)` is `true = true`,
which is provable, and `(false : Prop)` is `false = true`, which is refutable.
The objects differ: `(false : Prop)` is the equation `false = true`, not the
proposition `False`.

## `Decidable`

A proposition `p` is **decidable**
when there is a procedure that settles it and produces a proof of `p` or of
`¬p`. Lean records this as an instance of the class `Decidable p`.
-/

#print Decidable

/-!
The type `Decidable p` has two constructors, `isFalse` and `isTrue`, each
carrying the corresponding proof. A decision procedure therefore returns a bit
together with a proof, and the proof is what makes it usable in a proof.

The term `decide p` evaluates that procedure and returns the bit.
-/

#eval decide (2 + 2 = 4)
#eval decide (2 + 2 = 5)
#eval decide (3 < 2 ∧ 1 = 1)

/-!
Equality on `ℕ`, comparisons, and the connectives all have `Decidable`
instances, which is why the three expressions above compute.

The tactic `decide` closes a goal by running the decision procedure and using
the proof it produces.
-/

example : 2 + 2 = 4 := by decide

example : (7 : ℕ) ∣ 343 := by decide

example : ∀ n : Fin 5, n.val < 5 := by decide

/-!
In the last example, a `∀` over a *finite* type is decidable whenever
the statement being quantified is, because the procedure can then try every
case. Over `ℕ`, the procedure cannot try every case, since there are
infinitely many.

The tactic `decide` has two limits.

First, `decide` must actually run the decision procedure, and Lean's kernel
runs it again when it checks the proof. Plain arithmetic on `ℕ` is not the
problem: the kernel has built-in support for numeric literals, so even a
product of two six-digit numbers is settled instantly. Where `decide` becomes
impractical is when the procedure has to *enumerate* or *search* — a property
of every element of a large finite type, or `Nat.Prime p`, which is decided by
checking whether any number from `2` to `p - 1` divides `p`. The tactic
`norm_num` handles statements about `Nat.Prime`, since it reasons about
numerals rather than running them.

Second, not every proposition is decidable. There is no procedure that settles
an arbitrary `p : Prop`, so there is no `Decidable p` instance for a variable
`p`. The declaration `Classical.propDecidable` supplies an instance
for *every* proposition, using excluded middle, and the `classical` tactic
brings it into scope. Such an instance justifies writing `if p then _ else _`,
but it computes nothing, so definitions using it must be marked
`noncomputable`.
-/

-- succeeds: `n < 5` is decidable for a concrete `n`
example : (3 : ℕ) < 5 := by decide

-- fails: the goal contains the variable `p`, which `decide` cannot evaluate
-- example (p : Prop) : p ∨ ¬p := by decide

/-!
## Summary

|                      | `Bool`                                       | `Prop`       |
| :------------------- | :------------------------------------------- | :----------- |
| terms are            | the two values `true`, `false`               | propositions |
| terms of *those* are | —                                            | proofs       |
| written              | `b = true` when used as a statement          | directly     |
| computed by          | evaluation                                   | not computed |
| connected by         | `decide : (p : Prop) → [Decidable p] → Bool` |              |

## `rfl`, `norm_num` and `decide`

All three prove `2 + 2 = 4` on `ℕ`, for different reasons.

* `rfl` — both sides *reduce to the same term* by computation. No decision
  procedure is involved; the definition of `+` does the work. It fails on
  `(2 : ℝ) + 2 = 4`, where `+` does not reduce.
* `decide` — the proposition has a `Decidable` instance, and Lean runs it. Over
  `ℝ`, the instance is classical: it is built from `Classical.choice` and has
  nothing to run, so `decide` gets stuck, as the error message for the
  commented-out line below states.
* `norm_num` — arithmetic *reasoning* about numerals, using lemmas rather than
  evaluation.

On `ℕ`, all three succeed; over `ℝ`, only `norm_num` does.
-/

example : (2 : ℕ) + 2 = 4 := by rfl
example : (2 : ℕ) + 2 = 4 := by decide
example : (2 : ℕ) + 2 = 4 := by norm_num

-- over `ℝ` the `Decidable` instance is classical and computes nothing,
-- so only `norm_num` applies
example : (2 : ℝ) + 2 = 4 := by norm_num
-- example : (2 : ℝ) + 2 = 4 := by decide

/-!
## Exercises

Solutions: `solutions/06_Prop_vs_Bool.lean`. Further exercises: section 6 of
`07_Exercises.lean`.
-/

/-! ### 1 — a `∀` over a finite type
Why does this work, when the same statement over `ℕ` would not? -/

theorem ex1 : ∀ n : Fin 4, n.val + 1 ≤ 4 := sorry

/-! ### 2 — the limits of `decide`
Try `decide` on this one first, then use the tactic that is meant for it.
Write a comment saying what the difference is.

Over `ℕ`, the same statement is closed by `decide`. -/

theorem ex2 : (123456 : ℝ) * 654321 = 80779853376 := sorry

/-! ### 3 — a `Bool`-valued function
Define `evenB : ℕ → Bool` by recursion, so that `evenB n` is `true` exactly
when `n` is even. Then prove `evenB 10 = true`.

The statement is an equation between two `Bool` values. -/

-- def evenB : ℕ → Bool := sorry

theorem ex3 : True := sorry   -- replace by the statement about `evenB 10`
