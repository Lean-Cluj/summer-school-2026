/-
Copyright (c) 2026 Iulian Simion. All rights reserved.
Released under the 3-Clause BSD License as described in the file LICENSE.
Authors: Iulian Simion, assisted by Claude (Anthropic) and Gemini (Google)
-/
import Mathlib.Data.Real.Basic

/-!
# Rewriting

The morning introduced `rw [h]`: for `h : x = y` it replaces `x` by `y` in the
target (`logic/01_Propositions.lean`), then tries to close what remains
(`logic/03_Conjunction_Disjunction_Equivalence.lean`). This file takes the
two steps apart and then covers the tactic's further forms.

## `rewrite`, and what `rw` adds

The first step on its own is the tactic `rewrite [h]`, which replaces `x` by
`y` throughout the target and does nothing else.
-/

theorem sum_is_two (x : ℕ) (h : x = 1) : 1 + x = 2 :=
  by
    rewrite [h]
    rfl

/-!
After the rewrite, the target is `1 + 1 = 2`, and `rfl` closes it. The tactic
`rw` is `rewrite` followed by an attempt to close the target with a restricted
form of `rfl`. Here, the attempt succeeds, so `rw` finishes the proof alone.
-/

theorem sum_is_two' (x : ℕ) (h : x = 1) : 1 + x = 2 :=
  by
    rw [h]

/-!
The restriction is that the attempt unfolds only definitions marked
*reducible*, whereas `rfl` written as a separate step also unfolds ordinary
definitions. A target whose two sides agree only after such unfolding is
therefore left open by `rw` and closed by `rfl`, as in `solve_for_y` below.
Arithmetic on `ℕ` numerals is an exception, which is why `rw` finished
`sum_is_two'`: Lean evaluates it directly.

## Four further forms

A list rewrites with each equation in turn. Equations from the library are used
exactly like hypotheses: the signature of `mul_comm` has two explicit
arguments, and supplying them gives the equation to rewrite with, so
`mul_comm x y` is `x * y = y * x`.
-/

#check @mul_comm
#check @mul_assoc

theorem swap_factors (x y z : ℝ) : x * y * z = y * (x * z) :=
  by
    rw [mul_comm x y, mul_assoc y x z]

/-!
Multiplication groups to the left, so `x * y * z` stands for `(x * y) * z` and
needs no brackets; `y * (x * z)` groups the other way and needs them.

The arrow `←`, typed `\l`, rewrites with the equation reversed, replacing `y`
by `x`. It is needed when the target contains `y` but not `x`, as below:
`rw [h]` would look for `x`, find none, and fail.
-/

theorem rewrite_backwards (x y : ℝ) (h : x = y) (hx : 3 * x = 6) : 3 * y = 6 :=
  by
    rw [← h]
    exact hx

/-!
After the rewrite, the target is `3 * x = 6`, which is `hx`.

When several occurrences match, `nth_rw` selects which one to act on.
-/

theorem square_sum (x y c : ℕ) (h : x + y = c) : (x + y) * (x + y) = x * c + y * c :=
  by
    nth_rw 2 [h]
    rw [add_mul]

/-!
Here, `rw [h]` would replace both occurrences of `x + y`, whereas
`nth_rw 2 [h]` takes only the second.

Adding `at h` rewrites in a hypothesis rather than in the target. The morning
already used this form, in `logic/04_Existential_and_Negation.lean`; we
recall it here for completeness.
-/

theorem solve_for_y (x y : ℤ) (h1 : x = 3) (h2 : y = 4 * x - 3) : y = 9 :=
  by
    rw [h1] at h2
    rw [h2]
    rfl

/-!
The first rewrite turns `h2` into `y = 4 * 3 - 3`, and the second puts that in
place of `y`, leaving `4 * 3 - 3 = 9`.

This is the case described at the start. The numerals are in `ℤ`, not `ℕ`, so
the two sides agree only after unfolding the definitions of `*` and `-`: the
`rfl` attempt made by `rw` leaves the target open, and the tactic `rfl` closes
it.

The tactic `rwa` is `rw` followed by `assumption`, which closes the target with
a hypothesis whose type agrees with the target after unfolding definitions.
-/

theorem shift (a b : ℕ) (h : a = b) (h' : a + 1 = 5) : b + 1 = 5 :=
  by
    rwa [h] at h'

/-!
## Finding a lemma

The following tools help find a lemma in Mathlib.

* The naming convention lets you guess a name. A name describes the
  conclusion, in snake case, with words such as `nonneg` for `0 ≤`, and starts
  with a namespace such as `Nat.` when the lemma concerns one type. For
  example, "a sum of non-negatives is non-negative" is `add_nonneg`, and
  "`n - m = 0` exactly when `n ≤ m`" is `Nat.sub_eq_zero_iff_le`.
* The tactic `exact?` looks for a lemma closing the goal outright, and prints
  the one it finds.
* The tactic `apply?` is the same idea for a lemma that makes progress rather
  than finishing, and lists several candidates.
* The tactic `rw?` looks for a lemma that rewrites the goal.
* [Loogle](https://loogle.lean-lang.org/) searches by shape, for lemmas
  mentioning given constants or matching a pattern, while
  [LeanSearch](https://leansearch.net/) and
  [LeanExplore](https://www.leanexplore.com/) take a description in ordinary
  words.
-/

#check @add_nonneg
#check @Nat.sub_eq_zero_iff_le

example (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ a + b := add_nonneg ha hb

/-!
## Exercises

Solutions: `solutions/01_Rewriting.lean`. Further exercises: section 1 of
`09_Exercises.lean`.
-/

/-! ### 1 — a lemma with `rw`
A power whose exponent is a sum is the product of the powers. Find this lemma
and close the goal with `rw`. -/

theorem ex1 (a m n : ℕ) (h : m = 2) : a ^ (m + n) = a ^ 2 * a ^ n := sorry

/-! ### 2 — a lemma with `rwa`
The absolute value of a product is the product of the absolute values. Find
this lemma and close the goal with `rwa`. -/

theorem ex2 (x y : ℝ) (h : |x| * |y| = 6) : |x * y| = 6 := sorry

/-! ### 3 — one occurrence only
Here, `rw [h]` would rewrite *both* occurrences of `a`, leaving `b + b = 7`,
which `h2` does not prove. Rewrite only the first, with `nth_rw`. -/

theorem ex3 (a b : ℕ) (h : a = b) (h2 : b + a = 7) : a + a = 7 := sorry
