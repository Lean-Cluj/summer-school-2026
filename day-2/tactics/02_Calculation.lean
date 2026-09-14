/-
Copyright (c) 2026 Iulian Simion. All rights reserved.
Released under the 3-Clause BSD License as described in the file LICENSE.
Authors: Iulian Simion, assisted by Claude (Anthropic) and Gemini (Google)
-/
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

/-!
# Calculation

The proof below establishes a polynomial identity by rewriting, with seven
rewrites drawn from five library equations.
-/

theorem expand_by_rw (x y : ℝ) : (x + y) * (x + y) = x * x + 2 * (x * y) + y * y :=
  by
    rw [mul_add, add_mul, add_mul]
    rw [← add_assoc, add_assoc (x * x)]
    rw [mul_comm y x, ← two_mul]

/-!
## `ring` uses ring axioms

The tactic `ring`, which needs every commutative ring axiom except the existence
of negatives, proves the same goal outright.
-/

theorem expand (x y : ℝ) : (x + y) * (x + y) = x * x + 2 * (x * y) + y * y :=
  by ring

/-!
It normalises both sides into a canonical polynomial form and compares the
results, so it proves any equation that follows from the axioms alone. That
covers `ℤ`, `ℚ` and `ℝ`, and also `ℕ`.

What `ring` cannot do is use a hypothesis. It knows the axioms and nothing
about the terms in the context.
-/

-- does not close the goal: `ring` does not use `h`
-- example (x y : ℝ) (h : x = y) : x + 1 = y + 1 := by ring

/-!
### Denominators

The tactic `ring` handles division, up to a point. It treats `x / y` as
`x * y⁻¹` and normalises accordingly, so `x / 2 + x / 2 = x` is a `ring` goal.
-/

example (x : ℝ) : x / 2 + x / 2 = x := by ring

/-!
It cannot *cancel* a division. Division in Lean is a total function: `x / 0` is
defined, and its value is `0`. Consequently, `a / a = 1` is false when `a = 0`,
and `ring` cannot prove it. A statement that depends on a denominator being
non-zero must include that hypothesis.

The tactic `field_simp` uses such a hypothesis. It puts the expression over a
common denominator and clears it. Any equation that remains has no
denominators, and `ring`, called as a separate step, can finish it.
-/

example (x y : ℝ) (hx : x ≠ 0) : (y / x) * x = y := by field_simp

/-!
## `norm_num` works on the numbers

Where `ring` works from the axioms, `norm_num` works on the numerals. It
evaluates the numerical parts of a target, sums, products, quotients and powers
of numerals, and closes it when what remains is a numerical fact. Inequalities
count as such facts.
-/

theorem numeric_eq : (4 : ℝ) + 3 = 7 := by norm_num
theorem numeric_lt : (2 : ℝ) / 5 < 1 / 2 := by norm_num

/-!
The tactic `ring` also proves the first, since `4 + 3 = 7` follows from the
ring axioms and `ring` normalises numerals along with everything else. It
cannot prove the second, since it proves equations only.

Terms may be handed to `norm_num` in brackets, as to `rw`, and are used as
rewrite rules while the arithmetic is evaluated.
-/

theorem with_hyp (a : ℝ) (h : a = 3) : 2 + 2 + a = 4 + 3 := by norm_num [h]

/-!
Underneath `norm_num` is `simp`, the general rewriting tactic, together with
procedures that evaluate arithmetic. We return to `simp` in
`06_Stronger_Tactics.lean`.

## `calc` writes a chain of steps

Rewriting uses a hypothesis only where its left-hand side occurs in the goal;
`ring` rearranges the goal but uses no hypothesis. When both are needed, the
proof can be written as a chain of equalities, each step with its own proof,
and `calc` is the notation for that chain.
-/

theorem quarter {u v : ℚ} (h1 : 4 * u + v = 3) (h2 : v = 2) : u = 1 / 4 :=
  calc
    u = ((4 * u + v) - v) / 4 := by ring
    _ = (3 - 2) / 4 := by rw [h1, h2]
    _ = 1 / 4 := by norm_num

/-!
The first line states the term the chain starts from and the first step taken
from it. In every later line, `_` stands for the right-hand side of the line
above, so the chain reads downward and the whole establishes that the first
term equals the last. Each step is proved independently, here by `ring`, by
`rw` with the two hypotheses, and by `norm_num`.

The relations of consecutive steps must compose; for a chain of equalities they
always do.

The proof rearranges the expression until a hypothesis applies, substitutes,
and then simplifies. The same three steps prove a statement about a polynomial
remainder.
-/

theorem remainder {t : ℚ} (ht : t ^ 2 - 4 = 0) :
    t ^ 4 + 3 * t ^ 3 - 3 * t ^ 2 - 2 * t - 2 = 10 * t + 2 :=
  calc
    t ^ 4 + 3 * t ^ 3 - 3 * t ^ 2 - 2 * t - 2
        = (t ^ 2 + 3 * t + 1) * (t ^ 2 - 4) + 10 * t + 2 := by ring
    _ = (t ^ 2 + 3 * t + 1) * 0 + 10 * t + 2 := by rw [ht]
    _ = 10 * t + 2 := by ring

/-!
The first step divides the polynomial by `t ^ 2 - 4` and records the result,
which is an identity and so is proved by `ring`; the second uses the
hypothesis; the third clears the zero.

A `calc` chain is a term. None of these proofs opens with `by`, and `ring`
and `rw` appear only inside the individual steps.

## `have` names an intermediate fact

The tactic `have` states a proposition, takes a proof of it, and adds it to the
context under a name. Below, it records an intermediate fact proved by a `calc`
chain, and `linarith` concludes from that fact.
-/

theorem bound_x (x : ℝ) (hx : x ≥ 2 * x + 1) : x ≤ -1 :=
  by
    have h : x + 1 ≤ 0 :=
      calc
        x + 1 = (2 * x + 1) - x := by ring
        _ ≤ x - x := by linarith
        _ = 0 := by ring
    linarith

/-!
## Exercises

Solutions: `solutions/02_Calculation.lean`. Further exercises: section 2 of
`09_Exercises.lean`.
-/

/-! ### 1 — with `rw`, then with `ring`
Prove it first using `rw` only, five rewrites suffice, and then again with
`ring`. To find a lemma, use the tools described in `01_Rewriting.lean`. -/

theorem ex1 (p q r s : ℝ) : p * (q + r) * s = p * (r * s) + p * (q * s) := sorry

theorem ex1' (p q r s : ℝ) : p * (q + r) * s = p * (r * s) + p * (q * s) := sorry

/-! ### 2 — a numerical inequality
One tactic. Say why `ring` cannot prove it. -/

theorem ex2 : (3 : ℝ) / 7 < 1 / 2 := sorry

/-! ### 3 — a chain with a hypothesis
Prove `x = 3` from `2 * x + 3 * y = 12` and `y = 2`, with a `calc` chain whose
steps are justified by `ring`, `rw` and `norm_num`. -/

theorem ex3 (x y : ℝ) (h1 : 2 * x + 3 * y = 12) (h2 : y = 2) : x = 3 := sorry
