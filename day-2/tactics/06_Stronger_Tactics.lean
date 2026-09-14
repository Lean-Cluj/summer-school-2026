/-
Copyright (c) 2026 Iulian Simion. All rights reserved.
Released under the 3-Clause BSD License as described in the file LICENSE.
Authors: Iulian Simion, assisted by Claude (Anthropic) and Gemini (Google)
-/
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Aesop

/-!
# Stronger tactics

The tactics in this file take on a goal as a whole and **search** for a proof
of it, choosing the steps themselves. A search may fail on a goal that is true.

## `simp`

The tactic `simp` is the general rewriting tactic and the most used tactic in
Mathlib. It rewrites the target with the library lemmas marked `@[simp]`,
repeatedly, until nothing more applies.

The tactic `rw` applies the rules it is given, once each; `simp` applies a
whole collection, repeatedly.
-/

-- the lemma `Nat.zero_add` is tagged `@[simp]`, so `simp` finds it without
-- being told
example (x : ℕ) : 0 + x = x := by simp

/-!
Three variants: adding a local fact in brackets
uses it as a further rewrite rule; adding `at h` simplifies a hypothesis
instead of the target; and `simp only [...]` uses just the lemmas named and
nothing else.
-/

example (x y : ℕ) (h : y = 0) : x + y = x := by simp [h]

example (x y : ℕ) (h : x + 0 = y) : x = y :=
  by
    simp at h
    exact h

example (x : ℕ) : 0 + x = x := by simp only [Nat.zero_add]

/-!
A bare `simp` depends on the whole `@[simp]` set, which changes as Mathlib
changes; `simp only` fixes the rewrites used. The tactic `simp?` reports the
lemmas a `simp` call used, as a `simp only` call.

The tactic `norm_num` uses `simp` together with procedures that evaluate
arithmetic. Plain `simp` evaluates arithmetic on numerals in `ℕ` and `ℤ`;
`norm_num` extends this to other types, such as `ℚ`, `ℝ` and `ℂ`, and to
division and inverses.

## `nlinarith`

The tactic `nlinarith` runs `linarith` after adding the facts that linearity
ruled out: the non-negativity of each square occurring in the problem, and the
product of each pair of hypotheses. This proves the goal below, which
`linarith` cannot, since `x ^ 2` and `y ^ 2` are non-linear.
-/

theorem sum_sq_by_nlinarith {x y : ℤ} (hx : x ≥ 2) : x ^ 2 + y ^ 2 ≥ 4 := by nlinarith

/-!
Over `ℝ`, it does not prove `x ^ 4 + 1 ≥ x ^ 3 + x`, which holds because the
difference factors as `(x - 1) ^ 2 * (x ^ 2 + x + 1)`, a product of two
non-negative factors.

Extra facts may be supplied in brackets.
-/

example (a b : ℝ) : a * b ≤ (a ^ 2 + b ^ 2) / 2 := by nlinarith [sq_nonneg (a - b)]

/-!
## `grind`

The tactic `grind` proceeds differently, by equality reasoning, instantiation
of library lemmas marked for it, case analysis, and calls to solvers for linear
arithmetic and for commutative rings. That combination lets it handle goals
where logic, equality and arithmetic are mixed.
-/

theorem quarter_by_grind {u v : ℚ} (h1 : 4 * u + v = 3) (h2 : v = 2) : u = 1 / 4 := by grind

-- from `f x = f y`, congruence gives `f (f x) = f (f y)`, contradicting `h2`
example (f : ℤ → ℤ) (x y : ℤ) (h1 : f x = f y) (h2 : f (f x) ≠ f (f y)) : False := by grind

/-!
The file `02_Calculation.lean` proves the first of these by a `calc` chain
using `ring`, `rw` and `norm_num`. The tactic `grind` does not unfold
`≡ [ZMOD n]`, so, as with `omega`, a congruence goal needs its definition
unfolded.

## `aesop`

The tactic `aesop`, short for *Automated Extensible Search for Obvious
Proofs*, searches for a proof using a set of rules: `apply` and `intro` steps,
together with `simp` and Mathlib's simp set. It is suited to goals that are
mainly logical rather than arithmetical.
-/

theorem aesop_example (p q : Prop) (h : ¬p → ¬q) : q → p := by aesop

/-!
## Classical reasoning in these searches

The tactics `grind` and `nlinarith` argue by contradiction, as `by_contra`
does, so their proofs are classical. The tactic `aesop` has no such step of its
own, and alone it will not prove `p ∨ ¬p`; its proofs are classical when the
lemmas it finds are, as for the example below.
-/

#print axioms aesop_example

/-!
Which axioms a proof found by search depends on is shown by `#print axioms`,
not by the name of the tactic.

## Search and chain

A successful search produces a proof term without displaying its steps. A
`calc` chain states each step together with the fact that justifies it, so
writing one means choosing a tactic or lemma for every step; a search makes
that choice itself.

A search is also run again every time the file is checked, and what it finds
can change when Mathlib changes. Once it has succeeded, its `?` form, such as
`simp?`, `aesop?` or `grind?`, prints a narrower call or a script that can
replace it, for example `simp only [...]`;
`appendix/02_Maintenance_Utilities.lean` shows `simp?` at work.
-/

/-!
## Exercises

Solutions: `solutions/06_Stronger_Tactics.lean`. Further exercises: section 6 of
`09_Exercises.lean`.
-/

/-! ### 1 — `simp` with a local fact
Add the hypothesis to the simp set. -/

theorem ex1 (x y : ℕ) (h : y = 0) : x + y + 0 = x := sorry

/-! ### 2 — beyond `linarith`
This is not linear. Recall that `nlinarith` adds the non-negativity of the
squares occurring in the problem. -/

theorem ex2 (x y : ℝ) (h : y > 0) : x ^ 2 + y > 0 := sorry

/-! ### 3 — a mixed goal
Logic, equality and arithmetic at once. One word. -/

theorem ex3 (f : ℤ → ℤ) (x y : ℤ) (h1 : x = y) (h2 : f x ≠ f y) : False := sorry
