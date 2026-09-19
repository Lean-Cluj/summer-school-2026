/-
Copyright (c) 2026 Iulian Simion. All rights reserved.
Released under the 3-Clause BSD License as described in the file LICENSE.
Authors: Iulian Simion, assisted by Claude (Anthropic) and Gemini (Google)
-/
import Mathlib.Data.Real.Basic
import Mathlib.Data.Int.ModEq
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.GCongr

/-!
# Inequalities and congruences

Besides equality, this file concentrates on two relations: `≤` and
congruence. Each is built in a different way, and the construction determines
which tactics apply to it.

# Inequalities

The proposition `a = b` is notation for `Eq a b`, and `Eq` is one inductive
declaration serving every type. There is no such declaration for `≤`. It is a
**type class** carrying a single field.
-/

#print LE

/-!
The field takes two terms of `α` and returns a proposition, and `a ≤ b` is
notation for `LE.le a b`, as `a < b` is for `LT.lt a b`.
-/

#check LE.le 4 5   -- 4 ≤ 5 : Prop
#check LT.lt 4 5   -- 4 < 5 : Prop

/-!
Each type supplies its own instance, found by the elaborator from the type at
which `≤` is used, so `≤` on `ℕ` and `≤` on `ℝ` are different relations behind
one notation.

The class `LE` has a single field, `le`, and fixes only the notation.
It does not say that the relation is reflexive or transitive, and an instance
could supply any relation at all. That content comes from further classes:
`Preorder` extends `LE`, and an instance of it must also supply proofs of
reflexivity and transitivity. The library theorems `le_refl` and `le_trans`
below return those proofs. Every type used here has such an instance.
-/

section
variable (x y z : ℝ) (h : x ≤ y) (h' : y ≤ z)

#check (le_refl x : x ≤ x)
#check (le_trans h h' : x ≤ z)
end

/-!
## Chaining inequalities

The steps of a `calc` chain need not all be equalities. They may mix `=` with
`≤`, `<`, `≥` and `>`, provided consecutive relations compose into one: an
equality composes with any of them, inequalities pointing the same way compose
with each other, and a chain of `≥` steps containing one `>` proves `>`. What a
chain cannot do is turn around, since nothing composes `≤` with `≥`.
Transitivity is what makes the composition possible, the rule joining two `≤`
steps being `le_trans` itself.

Since `ring` proves equations only, an inequality step is proved by other
means, such as the tactics `rel`, `positivity` and `linarith` below.

## `rel` uses an inequality as `rw` uses an equation

Given proofs in brackets, `rel` replaces a subterm by a larger or smaller one,
checking that the position is monotone.
-/

theorem sum_ge {a b : ℚ} (h1 : 3 ≤ a) (h2 : a + 2 * b ≥ 4) : a + b ≥ 3 :=
  calc
    a + b = ((a + 2 * b) + a) / 2 := by ring
    _ ≥ (4 + 3) / 2 := by rel [h1, h2]
    _ ≥ 3 := by norm_num

/-!
The first step is an identity, which `ring` proves. The second replaces
`a + 2 * b` by `4` and `a` by `3`. Both replacements are decreases, given by
`h2` and `h1`, and both occur where decreasing an argument decreases the whole,
which is what `rel` verifies. The third is numerical.

The chain states the new expression, here `(4 + 3) / 2`. The tactic `rel`
compares it with the line above and checks each difference against the named
hypotheses; it does not produce the new expression itself.

A step may equally be justified by a term rather than a tactic.
-/

theorem sum_sq_ge {x y : ℤ} (hx : x ≥ 2) : x ^ 2 + y ^ 2 ≥ 4 :=
  calc
    x ^ 2 + y ^ 2 ≥ 2 ^ 2 + y ^ 2 := by rel [hx]
    _ = 4 + y ^ 2 := by ring
    _ ≥ 4 := le_add_of_nonneg_right (sq_nonneg y)

/-!
The first step replaces `x` by `2` inside the square. The tactic `rel` accepts
it because `hx` is an inequality in the same direction as the step, and squaring
preserves `≤` when the smaller base is non-negative, here `0 ≤ 2`, which `rel`
proves itself. The last is an inequality proved by a term: `sq_nonneg y` is a
proof of `0 ≤ y ^ 2`, and `le_add_of_nonneg_right` carries a proof of `0 ≤ b`
to one of `a ≤ a + b`.

The general form of `rel` is the tactic `gcongr`, which strips identical
structure from both sides of an inequality and reduces it to the inner
comparisons. The tactic `rel` must prove these from the listed hypotheses, while
`gcongr` leaves those it cannot prove as new goals.
-/

example (x y : ℝ) (hx : 0 ≤ x) (h : x ≤ y) : x ^ 3 ≤ y ^ 3 := by gcongr

/-!
## `positivity`

Some steps assert only that an expression is positive, non-negative or
non-zero, and `positivity` proves those. It establishes such a fact for each
part of the expression and combines them, a square being non-negative and a sum
of non-negatives non-negative; for a variable, it looks for a hypothesis such
as `0 < x`. The tactics `rel` and `gcongr` call it for their side conditions,
such as `0 ≤ 2` in `sum_sq_ge`.
-/

theorem sum_sq_ge' {x y : ℤ} (hx : x ≥ 2) : x ^ 2 + y ^ 2 - 4 ≥ 0 :=
  calc
    x ^ 2 + y ^ 2 - 4 ≥ 2 ^ 2 + y ^ 2 - 4 := by rel [hx]
    _ = y ^ 2 := by ring
    _ ≥ 0 := by positivity

-- for the variable `x`, `positivity` uses the hypothesis `hx : 0 < x`
example (x : ℝ) (hx : 0 < x) : 0 < x ^ 3 + x := by positivity

/-!
This is the previous theorem with the `4` moved across, and the chain ends
where `positivity` applies. The tactic does not prove the theorem outright:
`x ^ 2 + y ^ 2 - 4` contains a subtraction, and `positivity` cannot show from
the parts that a difference is non-negative. What it proves is the last step,
`y ^ 2 ≥ 0`.

## `linarith`

Where `ring` proves what follows from the commutative ring axioms, `linarith`
proves what follows *linearly* from the hypotheses in the context. It argues by
contradiction, as `by_contra` does (`logic/05_Classical_Logic.lean`): it
assumes the negation of the target and finds a linear combination of the
hypotheses and that negation that gives `0 < 0`. A chain of inequalities is thus
settled in one step.
-/

theorem chain_lt (a b c d e : ℝ) (h0 : a ≤ b) (h1 : b < c) (h2 : c ≤ d) (h3 : d < e) :
    a < e := by linarith

/-!
Linearity is the limit. The tactic multiplies hypotheses by non-negative
constants and sums the results, but it never multiplies two hypotheses together,
so it cannot prove `0 < x * y` from `0 < x` and `0 < y`. A non-linear term is
not rejected: it is treated as an opaque atom about which nothing is known.
-/

-- fails: `x ^ 2` is an atom, and there is no fact about it
-- example (x : ℝ) : x ^ 2 ≥ 0 := by linarith

/-!
Since `linarith` searches for a linear combination that gives `0 < 0`, a failure
means only that it found none, not that the statement is false: `x ^ 2 ≥ 0` is
true, and `linarith` still fails on it. The tactic `positivity` proves it, and
so does `nlinarith`, which runs `linarith` after adding facts such as the
non-negativity of each square in the problem. We return to `nlinarith` in
`06_Stronger_Tactics.lean`.

# Congruences

Equality is an inductive declaration and `≤` is the field of a type class. A
congruence of integers is built a third way, as an ordinary definition.
-/

#print Int.ModEq

/-!
The notation `a ≡ b [ZMOD n]` stands for `Int.ModEq n a b`, and the definition
says what it means: `a` and `b` leave the same remainder on division by `n`.
As opposed to `Eq` and `≤`, no inductive type is declared and no instance is
searched for. The proposition `a ≡ b [ZMOD n]` is the equation `a % n = b % n`,
written with its own notation.
-/

#check (5 : ℤ) ≡ 8 [ZMOD 3]

/-!
A definition unfolds whenever definitional equality is checked, so a congruence
between numerals is settled by computation, as an equality between numerals
is: both `5 % 3` and `8 % 3` reduce to `2`.
-/

theorem five_eight : (5 : ℤ) ≡ 8 [ZMOD 3] := rfl

/-!
Congruence is an equivalence relation: the Mathlib theorems `Int.ModEq.refl`,
`Int.ModEq.symm` and `Int.ModEq.trans` prove reflexivity, symmetry and
transitivity. Three further theorems build congruences from
congruences: `Int.ModEq.add` sends proofs of `a ≡ b [ZMOD n]` and
`c ≡ d [ZMOD n]` to a proof of `a + c ≡ b + d [ZMOD n]`, `Int.ModEq.mul` does
the same for products, and `Int.ModEq.pow` raises both sides to a power.
Together they say that congruence is preserved by the ring operations, which is
what makes calculating with it possible, and they are what `rel` uses on a
congruence step.

In Mathlib, the ring ℤ/nℤ is a separate type, `ZMod n`. For `n : ℕ`, the
theorem `ZMod.intCast_eq_intCast_iff` states that `a ≡ b [ZMOD n]` holds exactly
when `a` and `b` are equal as elements of `ZMod n`. This file works in `ℤ`, with
the relation.

## Chaining congruences

A `calc` chain may mix congruence steps with equalities, as the chains above
mixed inequalities with them. The pattern is to replace a term by one it is
congruent to, compute with the result, and read off the answer.
-/

theorem prod_cong {a b : ℤ} (ha : a ≡ 2 [ZMOD 7]) (hb : b ≡ 3 [ZMOD 7]) :
    a * b ≡ 6 [ZMOD 7] :=
  calc a * b ≡ 2 * b [ZMOD 7] := by rel [ha]
    _ ≡ 2 * 3 [ZMOD 7] := by rel [hb]
    _ = 6 := by norm_num

/-!
Each of the first two steps replaces one factor by a number congruent to it,
and `rel` justifies both as it did for inequalities. For the first, it builds
`Int.ModEq.mul ha (Int.ModEq.refl b)`, which multiplies `a ≡ 2` by `b ≡ b` to
give `a * b ≡ 2 * b`. The two congruences compose because `Int.ModEq.trans`
joins them, as `ge_trans` joined the two `≥` steps of `sum_ge`. The last step
is an equation between numerals, which `norm_num` settles.

Divisibility is the other face of the same relation. The theorem
`Int.modEq_iff_dvd` states that `a ≡ b [ZMOD n]` holds exactly when
`n ∣ b - a`, so a statement in either form may be turned into the other.
Divisibility is transitive, so it chains as well.
-/

theorem three_dvd {n : ℤ} (h : 3 ∣ n) : 3 ∣ n ^ 2 + n :=
  calc (3 : ℤ) ∣ n := h
    _ ∣ n * (n + 1) := dvd_mul_right n (n + 1)
    _ = n ^ 2 + n := by ring

/-!
The first step is the hypothesis, the second the library theorem
`dvd_mul_right`, which states that `a ∣ a * b`, and the third rearranges the
product. Both divisibility steps are proved by terms: neither replaces a
subterm of a larger expression, which is what `rel` does.

## `omega`

The tactic `omega` handles linear arithmetic over `ℤ` and `ℕ`, and it
understands remainder `%`, integer division `/` and divisibility `∣` when the
modulus or divisor is a numeral.
Integer division discards the remainder, so `7 / 2` is `3`, and subtraction on
`ℕ` is truncated at `0`, so `3 - 7` is `0`; `omega` accounts for both.
As with `linarith`, a failure does not mean that the statement is false: Lean's
implementation of `omega` does not prove every true statement of this kind.
-/

theorem shift_mod (a : ℤ) (h : a % 5 = 3) : (a + 2) % 5 = 0 := by omega

theorem dvd_lin {n : ℕ} (h : 5 ∣ n) : 5 ∣ 3 * n + 10 := by omega

example (n : ℕ) (h : n ≤ 3) : n - 5 = 0 := by omega

/-!
The congruence notation is a different matter. Since `a ≡ b [ZMOD n]` stands
for a definition, and `omega` does not see through it, the unfolding is left to
the proof. The tactic `unfold` replaces a name by its definition; on its own it
acts on the target, and `at *` unfolds everywhere, hypotheses included.
-/

theorem five_eight' : (5 : ℤ) ≡ 8 [ZMOD 3] :=
  by
    unfold Int.ModEq
    omega

theorem shift_cong (a : ℤ) (h : a ≡ 3 [ZMOD 5]) : a + 2 ≡ 0 [ZMOD 5] :=
  by
    unfold Int.ModEq at *
    omega

/-!
The second proof needs `at *`, since unfolding the target alone would leave the
hypothesis folded and `omega` with no constraint it can use. What unfolding
exposes is an equation between remainders, which `omega` can decide.

Linearity is the limit here as it was for `linarith`. Neither of the examples
above, `prod_cong` and `three_dvd`, yields to `omega`, unfolded or not:
`a * b` and `n ^ 2` are products of unknowns, which `omega`, like `linarith`,
treats as atoms about which the hypotheses say nothing.

## Moving between number types

Statements mixing `ℕ`, `ℤ`, `ℚ` and `ℝ` contain **coercions**: the Infoview
shows `↑n` where a natural number is used as a real. The real number `(n : ℝ)`
and the natural number `n` are different terms, so a goal can fail to match a
hypothesis or a lemma because of a coercion.

The tactic `push_cast` moves coercions inward, turning `((a + b : ℕ) : ℝ)` into
`(a : ℝ) + (b : ℝ)`. The tactic `norm_cast` moves them outward, turning
`(a : ℝ) + (b : ℝ) = (c : ℝ)` into `a + b = c`; if the result is one of the
hypotheses, it also closes the goal.
-/

example (a b : ℕ) : ((a + b : ℕ) : ℝ) = (a : ℝ) + (b : ℝ) := by push_cast; ring

example (a b : ℕ) (h : a = b) : (a : ℝ) = (b : ℝ) := by norm_cast

/-!
## Summary

The three relations build propositions, and each relation is built by a
different mechanism.

| Notation         | Stands for        | Built as                                                        |
| :--------------- | :---------------- | :-------------------------------------------------------------- |
| `a = b`          | `Eq a b`          | an inductive declaration with one constructor                   |
| `a ≤ b`          | `LE.le a b`       | the field of a type class, supplied at each type by an instance |
| `a ≡ b [ZMOD n]` | `Int.ModEq n a b` | a definition, unfolding to `a % n = b % n`                      |

The declaration `Eq` serves every type, so equality means the same everywhere.
The class `LE` fixes the notation alone, so `≤` means at each type whatever
that type's instance supplies. Since `Int.ModEq` is a definition, it unfolds,
which is why `rfl` proves a congruence between numerals and why `omega` needs
`unfold` first.

The tactics, and what each may draw on:

| Tactic                                   | What it does                                                  | Uses the hypotheses                       |
| :--------------------------------------- | :------------------------------------------------------------ | :---------------------------------------- |
| `rfl`                                    | closes a goal whose two sides reduce to a common normal form  | no                                        |
| `rw [h]`, `nth_rw 2 [h]`, `rw [h] at h'` | rewrites with an equation                                     | only `h`                                  |
| `ring`                                   | closes an equation following from the commutative ring axioms | no                                        |
| `field_simp`                             | clears denominators, using non-vanishing hypotheses           | yes                                       |
| `norm_num [h]`                           | evaluates numerals and closes a numerical goal                | only `h`                                  |
| `rel [h]`                                | uses an inequality or congruence on a subterm                 | `h`, and `positivity` for side conditions |
| `gcongr`                                 | the same, leaving what it cannot prove as new goals           | yes                                       |
| `positivity`                             | closes `0 < e`, `0 ≤ e` or `e ≠ 0`                            | for its atoms                             |
| `linarith`                               | closes what follows linearly from the hypotheses              | yes                                       |
| `omega`                                  | closes a linear goal over `ℤ` or `ℕ`, with `%`, `/`, `∣`      | yes                                       |
| `unfold`                                 | replaces a name by its definition                             | no                                        |
| `push_cast [h]`                          | moves coercions inward                                        | only `h`                                  |
| `norm_cast`                              | moves coercions outward                                       | yes                                       |

Two moves organise a proof rather than close a goal: `have` proves an
intermediate proposition and names it, and `calc` chains steps, each with its
own justification.
-/

/-!
# Exercises

Solutions: `solutions/03_Inequalities_and_Congruences.lean`. Further exercises: section 3 of
`09_Exercises.lean`.
-/

/-! ## 1 — a chain with a `rel` step
Prove it with a chain whose inequality step is a `rel`. Confirm that `linarith`
does not prove it on its own, and say why. -/

theorem ex1 (x : ℤ) (hx : x ≥ 3) : 2 * x ^ 3 - 4 * x ^ 2 + 3 * x ≥ 3 := sorry

/-! ## 2 — a sign
One tactic. It reads the structure of the expression, and picks the hypothesis
out of the context when it reaches the bare `x`. -/

theorem ex2 (x : ℝ) (hx : 0 < x) : 0 < x ^ 3 + x := sorry

/-! ## 3 — a chain of congruences
Prove it with a chain of congruence steps. The chain cannot end on an equation
between numerals as `prod_cong` does; say what closes its last step instead. -/

theorem ex3 (a b : ℤ) (ha : a ≡ 4 [ZMOD 5]) (hb : b ≡ 3 [ZMOD 5]) :
    a * b ≡ 2 [ZMOD 5] := sorry
