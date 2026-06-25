/-
Copyright (c) 2026 Iulian Simion. All rights reserved.
Released under the 3-Clause BSD License as described in the file LICENSE.txt.
Authors: Iulian Simion

Note: Parts of this file were synthesized with the assistance of Gemini 3.1 Pro.
-/
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Analysis.SpecialFunctions.Exp


/-
  ## 1. `rfl` (Definitional Equality)

  The `rfl` tactic succeeds only if the left and right sides of an equation
  are *definitionally* equal — meaning Lean's kernel can compute them
  to the exact same normal form without needing external proofs or lemmas.
-/

-- Succeeds: `x + 0` evaluates definitionally to `x` by Lean's core rules.
example (x : ℕ) : x + 0 = x := by rfl

-- Fails: `0 + x` requires the inductive proof `Nat.zero_add`.
-- example (x : ℕ) : 0 + x = x := by rfl


/-
  ## 2. `simp` (Term Rewriting)

  `simp` extends `rfl` by navigating propositional equalities.
  It uses a massive library of lemmas tagged with `@[simp]`
  to repeatedly rewrite expressions from left to right
  until it reaches a simplified normal form.
-/

-- Succeeds: `simp` knows `Nat.zero_add` and rewrites `0 + x` to `x`.
example (x : ℕ) : 0 + x = x := by simp

-- Fails: `simp` struggles with unguided commutativity and associativity.
-- example (x y : ℝ) : (x + y) * (x - y) = x^2 - y^2 := by simp


/-
  ## 3. `gcongr` (Generalized Congruence)

  While `simp` substitutes equals for equals,
  `gcongr` extends structural reasoning to inequalities.
  It strips away identical outer layers of an expression
  by applying monotonicity lemmas,
  distilling the goal down to the core relation between variables.
-/
open Real

-- Succeeds: Strips away `exp` and `+ 5`, reducing the goal to `a ≤ b`.
example (a b : ℝ) (h : a ≤ b) : exp a + 5 ≤ exp b + 5 :=
  by gcongr

-- Fails: It cannot solve algebraic or arithmetic properties on its own.
-- example (a b : ℝ) (h : a ≤ b) : exp a + 5 ≤ exp b + 5 := by linarith


/-
  ## 4. `norm_num` (Numerical Normalization)

  Because `simp` relies on unary logic (treating `3` as `1 + 1 + 1`),
  it is completely unsuited for arithmetic.
  `norm_num` provides a specialized, highly optimized decision procedure
  to instantly evaluate closed numerical expressions using binary representations.
-/

-- Succeeds: Evaluates massive computations instantly.
example : 123456 * 654321 = 80779853376 := by norm_num

-- Fails: Strictly for numerical evaluation, not symbolic variables.
-- example (x : ℝ) : x + x = 2 * x := by norm_num


/-
  ## 5. `positivity` (Sign Analysis)

  `positivity` recursively traverses expressions to automatically prove
  strict positivity (`> 0`) or non-negativity (`≥ 0`) based on
  known structural rules (like squares or absolute values).
-/

-- Succeeds: Recursively knows squares and absolute values are ≥ 0.
example (x y : ℝ) : 0 < x^2 + |y| + 3 := by positivity

-- Fails: It evaluates signs, but does not solve general algebraic inequalities.
-- example (x : ℝ) (h : x > 5) : x > 4 := by positivity

/-
  ## 6. `ring` (Commutative Semiring Normalization)

  Moving into heavy symbolic algebra,
  `ring` parses polynomial expressions into a canonical sum-of-products form.
  If two algebraic expressions share the same normal form,
  `ring` closes the equality.
-/

-- Succeeds: Expands and matches canonical forms on both sides.
example (x y : ℝ) : (x + y) * (x - y) = x^2 - y^2 := by ring

-- Fails: `ring` is strictly for equalities, not `<` or `≤`.
-- example (x y : ℝ) (h : x < y) : x + 1 < y + 1 := by ring

/-
  ## 7. `field_simp` (Fractions and Fields)

  `ring` chokes immediately when division is introduced.
  `field_simp` acts as an aggressive pre-processor for algebraic fractions.
  It clears denominators and places expressions over a common denominator,
  bridging the gap so `ring` can finish the proof.

-/

-- Succeeds: `field_simp` transforms the fraction so `ring` can verify it.
example (x y : ℝ) (hx : x ≠ 0) : (y / x) * x = y := by
  field_simp
  --ring

-- Fails: `ring` alone sees `/` as an opaque function and fails.
-- example (x y : ℝ) (hx : x ≠ 0) : (y / x) * x = y := by ring

/-
  ## 8. `linarith` (Continuous Linear Arithmetic)

  Leaving pure equations behind, `linarith` handles linear inequalities
  over ordered rings (ℝ, ℚ). It gathers local hypotheses
  and uses Fourier-Motzkin elimination to find contradictions or prove bounds.
-/

-- Succeeds: Understands inequalities and combines transitive hypotheses.
example (x y z : ℝ) (h1 : x < y) (h2 : y < z) : x + 2 < z + 2 := by linarith

-- Fails: Cannot handle non-linear terms like `x^2`.
-- example (x : ℝ) : x^2 ≥ 0 := by linarith

/-
  ## 9. `omega` (Discrete Linear Arithmetic)

  While `linarith` treats variables continuously,
  `omega` uses Presburger arithmetic algorithms
  to understand the discrete boundaries of $ℕ$ and $ℤ$.
  It handles integer division, modulo,
  and the fact that there are no integers between $n$ and $n + 1$.
-/

-- Succeeds: Knows that for integers, if n < m, then n + 1 ≤ m.
example (n m : ℕ) (h : n < m) : n + 1 ≤ m := by omega

-- Fails: `linarith` treats `n` and `m` as abstract continuous variables.
-- example (n m : ℕ) (h : n < m) : n + 1 ≤ m := by linarith

/-
  ## 10. `nlinarith` (Non-linear Arithmetic)

  A heuristic wrapper around `linarith`.
  Before running standard elimination, it hunts for non-linear terms
  and dynamically injects fundamental non-linear truths into the context
  (e.g., `A^2 ≥ 0`, or `A * B ≥ 0` if both are positive).

-/

-- Succeeds: Injects `x^2 ≥ 0`, which combined with `y > 0` solves the goal.
example (x y : ℝ) (h : y > 0) : x^2 + y > 0 := by nlinarith

-- Fails: Cannot handle uninterpreted functions or raw logical contradictions.
-- example (f : ℤ → ℤ) (x y : ℤ) (h1 : f x = f y) (h2 : f (f x) ≠ f (f y)) : False := by nlinarith

/-
  ## 11. `grind` (SMT-style Global Automation)

  The most sophisticated solver in the Lean 4 standard toolkit.
  It abandons narrow specialization to act as an SMT-style global reasoning engine.
  It combines congruence closure, E-matching, and arithmetic
  into a single workflow to solve goals where logical connectives,
  uninterpreted functions, and math are heavily intertwined.

-/

-- Succeeds: `grind` globally tracks the equality `f x = f y` and applies
-- congruence to deduce `f (f x) = f (f y)`, exposing the contradiction.
example (f : ℤ → ℤ) (x y : ℤ) (h1 : f x = f y) (h2 : f (f x) ≠ f (f y)) : False := by
  grind






/- EXERCISE 1
    Find the solutions of the system,
    replace the correct values for `x` and `y` and
    complete the proof of the statement

    The `grind` tactic is not allowed.
-/
example : ∀ x y : ℝ, 2 * x + y = 7 ∧ 3 * x - 2 * y = 1 → x = sorry ∧ y = sorry := sorry
example : ∀ x y : ℝ, 2 * x + y = 7 ∧ 3 * x - 2 * y = 1 → x = 15/7 ∧ y = 19/7 :=
  by
    intro x y hxy
    obtain ⟨h₁,h₂⟩ := hxy
    exact ⟨by linarith, by linarith⟩


/- EXERCISE 2
    Find the solutions of the system.
    complete the proof of the statement by providing the solutions

    Notice that the `grind` tactic fails.
-/
example : ∃ x y : ℝ, -3 * x + 2 * y = 7 ∧ 2 * x + 4 * y = 3 :=
  by
    use -11/8, 23/16
    norm_num


/- EXERCISE 3
    Find the solutions of the quadratic equation,
    replace the correct values for `x` and
    complete the proof of the statement

    The `grind` tactic is not allowed.
-/
example : ∀ x : ℝ, 2 * x ^ 2 - 12 * x - 14 = 0 → x = sorry ∨ x = sorry := sorry
example : ∀ x : ℝ, 2 * x ^ 2 - 12 * x - 14 = 0 → x = 7 ∨ x = -1 :=
  by
    intro x hx
    have hx' : (x + 1) * (x - 7) = 0 :=
      calc
        (x + 1) * (x - 7) = (2 * x ^ 2 - 12 * x - 14)/2 := by ring
        _ = 0/2 := by rw [hx]
        _ = 0 := by ring
    have hx'' : x + 1 =0 ∨ x - 7 = 0 := eq_zero_or_eq_zero_of_mul_eq_zero  hx'
    obtain h₁ | h₂  := hx''
    · right
      linarith
    · left
      linarith
