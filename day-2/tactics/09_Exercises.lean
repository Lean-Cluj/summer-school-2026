/-
Copyright (c) 2026 Iulian Simion. All rights reserved.
Released under the 3-Clause BSD License as described in the file LICENSE.
Authors: Iulian Simion, assisted by Claude (Anthropic) and Gemini (Google)
-/
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Int.ModEq
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Push
import Aesop

/-!
# Further exercises for the afternoon

Further exercises on the afternoon's topics, one section per topic file
`01`–`06` and section 7 for `07` and `08`, each inside its own `namespace`. No section depends on another. Do
not use `grind` in sections 2 and 3; it is allowed in section 6.

Replace every `sorry` by a proof. Exercises 5.3 and 6.5 are answered in words,
and 7.2 and 7.3 start from commented-out stubs.

Solutions: `solutions/09_Exercises.lean`.
-/

/-! ## 1 — Rewriting

After `01_Rewriting.lean`. -/

namespace Rewriting

/-! ### 1.1 — rewriting in three steps
Use `mul_add` and `mul_comm`. The second is needed twice, at two different
places. All three rewrites fit in one `rw [...]`. -/

theorem ex1 (a b c : ℝ) : a * (b + c) = b * a + c * a := sorry

/-! ### 1.2 — one rewrite, two occurrences
A single `rw [h]` replaces every occurrence at once. -/

theorem ex2 (x y : ℕ) (h : x = y) : x + x = y + y := sorry

/-! ### 1.3 — rewriting backwards
The arrow `←` uses the equation right to left. -/

theorem ex3 (x y : ℝ) (h : x = y) : y = x := sorry

/-! ### 1.4 — find the lemma
Prove that a product of non-negative reals is non-negative. Try `exact?`, or
guess the name from the conventions in `01_Rewriting.lean`. -/

theorem ex4 (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ a * b := sorry

/-! ### 1.5 — rewriting to match a hypothesis
Rewrite, then close with `exact`. Then do it again in one line with `rwa`. -/

theorem ex5 (a b : ℕ) (h : a = b) (h' : b + 2 = 7) : a + 2 = 7 := sorry

end Rewriting

/-! ## 2 — Calculation

After `02_Calculation.lean`. Do not use `grind`. -/

namespace Calculation

/-! ### 2.1 — division with remainder
Prove `x ^ 3 = 4 * x` from `x ^ 2 - 4 = 0`. The first step of the chain is a
division with remainder: say what is divided by what. -/

theorem ex1 (x : ℝ) (h : x ^ 2 - 4 = 0) : x ^ 3 = 4 * x := sorry

/-! ### 2.2 — a denominator
The hypothesis is what lets the `x` cancel. -/

theorem ex2 (x y : ℝ) (hx : x ≠ 0) (h : y = 3 * x) : y / x = 3 := sorry

/-! ### 2.3 — an intermediate fact
Use `have` to establish `x + 1 ≤ 0` by a short chain, then finish with
`linarith`. -/

theorem ex3 (x : ℝ) (hx : x ≥ 2 * x + 1) : x ≤ -1 := sorry

end Calculation

/-! ## 3 — Inequalities and congruences

After `03_Inequalities_and_Congruences.lean`. Do not use `grind`. -/

namespace InequalitiesCongruences

/-! ### 3.1 — `positivity` needs the right shape
The tactic fails on this statement as it stands. Find the equality that turns
it into a goal `positivity` closes, and use a chain. -/

theorem ex1 (x : ℝ) : x ^ 2 + 2 * x + 1 ≥ 0 := sorry

/-! ### 3.2 — linear, in two ways
Do it twice: once with `linarith` alone, and once by proving a bound with
`have` and then finishing. -/

theorem ex2 (x y : ℝ) (h1 : x + y ≥ 1) (h2 : 2 * x - 3 * y ≥ 1) : x ≥ 4 / 5 := sorry

/-! ### 3.3 — no solution over `ℕ`
Which tactic knows that `3 * n = 10` is impossible for a natural number? -/

theorem ex3 (n : ℕ) (h : 3 * n = 10) : False := sorry

/-! ### 3.4 — divisibility chains too
Prove it by a chain of divisibility steps. Name the library theorem that
justifies the middle one. -/

theorem ex4 (n : ℤ) (h : 4 ∣ n) : 4 ∣ n ^ 2 + 3 * n := sorry

/-! ### 3.5 — `unfold` then `omega`
Then run the proof with `unfold Int.ModEq` in place of `unfold Int.ModEq at *`,
and account for what `omega` reports. -/

theorem ex5 (a : ℤ) (h : a ≡ 2 [ZMOD 4]) : a + 3 ≡ 1 [ZMOD 4] := sorry

end InequalitiesCongruences

/-! ## 4 — Case analysis

After `04_Cases.lean`. -/

namespace CaseAnalysis

/-! ### 4.1 — `rcases` on a disjunction -/

theorem ex1 (p q r : Prop) (h : p ∨ q) (hpr : p → r) (hqr : q → r) : r := sorry

/-! ### 4.2 — three cases, one tactic
Split, then close all three branches at once with `<;>`. -/

theorem ex2 (n : ℕ) (h : n = 2 ∨ n = 4 ∨ n = 6) : n % 2 = 0 := sorry

/-! ### 4.3 — no natural number solves `17n = 2`
Start with `push Not`, then split on whether `n` is zero or positive
(`Nat.eq_zero_or_pos`). -/

theorem ex3 : ¬∃ n : ℕ, 17 * n = 2 := sorry

/-! ### 4.4 — truncated subtraction and a square

`n ^ 2 - n = 0 ↔ n = 1 ∨ n = 0`

Subtraction on `ℕ` is truncated. Here, `n ^ 2 ≥ n` for every natural number, so
`n ^ 2 - n` is the true difference, and the statement also holds over `ℤ`,
where it reads `n * (n - 1) = 0`. The tactic `omega` handles only linear
arithmetic, so it does not prove this statement.

For the left-to-right direction, split `n` into the cases `0`, `1` and `k + 2`
with `obtain _ | _ | k := n`, and in the last case derive a contradiction.
The lemma `Nat.sub_eq_zero_iff_le` turns `n ^ 2 - n = 0` into `n ^ 2 ≤ n`. -/

theorem ex4 (n : ℕ) : n ^ 2 - n = 0 ↔ n = 1 ∨ n = 0 := sorry

end CaseAnalysis

/-! ## 5 — Induction

After `05_Induction.lean`. -/

namespace Induction

/-! ### 5.1 — the same shape as Example 1 of `05_Induction.lean` -/

theorem ex1 (n : ℕ) : 3 ^ n ≥ n + 1 := sorry

/-! ### 5.2 — powers of a rational ≥ 1
Model it on `rat_pow_pos` in `05_Induction.lean`. The tactic `gcongr` handles
the middle step. -/

theorem ex2 (q : ℚ) (hq : 1 ≤ q) (n : ℕ) : 1 ≤ q ^ n := sorry

/-! ### 5.3 — to answer in words
Exercises 2 and 3 of `05_Induction.lean` used different rules:
two-step induction for the sequence `v`, strong induction for the powers of
two. For each, write down the hypothesis the rule gives you in the step case,
and say why the other rule would not have served: what does exercise 2 not
need, and what does exercise 3 require that two hypotheses cannot supply? -/

end Induction

/-! ## 6 — Stronger tactics

After `06_Stronger_Tactics.lean`. The tactic `grind` is allowed. -/

namespace StrongerTactics

/-! ### 6.1 — `simp only`
Exercise 1 of `06_Stronger_Tactics.lean` proved this statement with
`simp`. Prove it again using `simp only` with the lemmas named, so that the
proof does not depend on the whole `@[simp]` set. Run `simp?` on the `simp`
proof to find out which lemmas to name. -/

theorem ex1 (x y : ℕ) (h : y = 0) : x + y + 0 = x := sorry

/-! ### 6.2 — supplying the missing square
This one needs a fact `nlinarith` does not add by itself. Give it
`sq_nonneg (a - b)` in brackets. -/

theorem ex2 (a b : ℝ) : a * b ≤ (a ^ 2 + b ^ 2) / 2 := sorry

/-! ### 6.3 — where `nlinarith` stops
The statement holds because the difference factors as
`(x - 1) ^ 2 * (x ^ 2 + x + 1)`. Confirm that `nlinarith` alone fails, then
prove it by supplying that factorisation as an intermediate fact. -/

theorem ex3 (x : ℝ) : x ^ 4 + 1 ≥ x ^ 3 + x := sorry

/-! ### 6.4 — a logical goal
This one is propositional rather than arithmetical. -/

theorem ex4 (p q r : Prop) (hpq : p → q) (hqr : q → r) : p → r := sorry

/-! ### 6.5 — to answer in words
Write out exercise 6.4 again as a term, `fun hp => hqr (hpq hp)`, and run
`#print axioms` on both versions. They differ. Account for the difference, and
say what it shows about reading a proof's dependencies off the tactic that
produced it. -/

end StrongerTactics

/-! ## 7 — Combinators and macros

After `07_Tactic_Combinators.lean` for 7.1, and `08_Macros.lean` for 7.2 and
7.3. The predicate `Even` is declared inside the namespace so that it does not
clash with Mathlib's. -/

namespace CombinatorsMacros

inductive Even : ℕ → Prop where
  | zero : Even 0
  | add_two : ∀ k : ℕ, Even k → Even (k + 2)

/-! ### 7.1 — split a conjunction, then close every branch
Combine `repeat' apply And.intro` with the expression from exercise 1 of
`07_Tactic_Combinators.lean`. -/

theorem ex1 : Even 4 ∧ Even 6 ∧ Even 8 := sorry

/-! ### 7.2 — a term macro
Define `ℚ³` as an abbreviation for `ℚ × ℚ × ℚ`, then define a triple of that
type and `#check` it. -/

namespace Ex2
-- macro "ℚ³" : term => sorry
-- def triple : ℚ³ := sorry
end Ex2

/-! ### 7.3 — an operator
Define `qdist x y := |x - y|` on `ℚ`, give it an infix notation of your
choosing, and prove that it is symmetric.

Hint: `abs_sub_comm`. Use a symbol that Mathlib does not already define, and
not the name `dist`, which Mathlib uses for distance. -/

namespace Ex3
-- def qdist (x y : ℚ) : ℚ := sorry
end Ex3

end CombinatorsMacros
