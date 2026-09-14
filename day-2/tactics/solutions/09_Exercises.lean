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

/-! # Solutions — Further exercises for the afternoon -/

/-! ## 1 — Rewriting -/

namespace Rewriting

-- 1.1
theorem ex1 (a b c : ℝ) : a * (b + c) = b * a + c * a :=
  by
    rw [mul_add, mul_comm a b, mul_comm a c]

-- 1.2
theorem ex2 (x y : ℕ) (h : x = y) : x + x = y + y :=
  by
    rw [h]

-- 1.3
theorem ex3 (x y : ℝ) (h : x = y) : y = x :=
  by
    rw [← h]

-- 1.4
theorem ex4 (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ a * b :=
  mul_nonneg ha hb

-- 1.5
theorem ex5 (a b : ℕ) (h : a = b) (h' : b + 2 = 7) : a + 2 = 7 :=
  by
    rw [h]
    exact h'

-- the same in one line
example (a b : ℕ) (h : a = b) (h' : b + 2 = 7) : a + 2 = 7 :=
  by
    rwa [h]

end Rewriting

/-! ## 2 — Calculation -/

namespace Calculation

-- 2.1
-- The first step divides `x ^ 3` by `x ^ 2 - 4`, with quotient `x` and
-- remainder `4 * x`.
theorem ex1 (x : ℝ) (h : x ^ 2 - 4 = 0) : x ^ 3 = 4 * x :=
  calc
    x ^ 3 = x * (x ^ 2 - 4) + 4 * x := by ring
    _ = x * 0 + 4 * x := by rw [h]
    _ = 4 * x := by ring

-- 2.2
theorem ex2 (x y : ℝ) (hx : x ≠ 0) (h : y = 3 * x) : y / x = 3 :=
  by
    rw [h]
    field_simp

-- 2.3
theorem ex3 (x : ℝ) (hx : x ≥ 2 * x + 1) : x ≤ -1 :=
  by
    have h : x + 1 ≤ 0 :=
      calc
        x + 1 = (2 * x + 1) - x := by ring
        _ ≤ x - x := by linarith
        _ = 0 := by ring
    linarith

end Calculation

/-! ## 3 — Inequalities and congruences -/

namespace InequalitiesCongruences

-- 3.1
-- The tactic `positivity` cannot read a sign off `x ^ 2 + 2 * x + 1`, since
-- `2 * x` may be negative. Completing the square turns it into a goal it does
-- close.
theorem ex1 (x : ℝ) : x ^ 2 + 2 * x + 1 ≥ 0 :=
  calc
    x ^ 2 + 2 * x + 1 = (x + 1) ^ 2 := by ring
    _ ≥ 0 := by positivity

-- 3.2
theorem ex2 (x y : ℝ) (h1 : x + y ≥ 1) (h2 : 2 * x - 3 * y ≥ 1) : x ≥ 4 / 5 :=
  by linarith

example (x y : ℝ) (h1 : x + y ≥ 1) (h2 : 2 * x - 3 * y ≥ 1) : x ≥ 4 / 5 :=
  by
    have h3 : 5 * x ≥ 4 := by linarith
    linarith

-- 3.3
theorem ex3 (n : ℕ) (h : 3 * n = 10) : False :=
  by omega

-- 3.4
-- The middle step is `dvd_mul_right : a ∣ a * b`.
theorem ex4 (n : ℤ) (h : 4 ∣ n) : 4 ∣ n ^ 2 + 3 * n :=
  calc (4 : ℤ) ∣ n := h
    _ ∣ n * (n + 3) := dvd_mul_right n (n + 3)
    _ = n ^ 2 + 3 * n := by ring

-- 3.5
-- With `unfold Int.ModEq` alone the hypothesis stays folded, so `omega` has no
-- constraint relating `a` to `2` and reports that it cannot prove the goal.
theorem ex5 (a : ℤ) (h : a ≡ 2 [ZMOD 4]) : a + 3 ≡ 1 [ZMOD 4] :=
  by
    unfold Int.ModEq at *
    omega

end InequalitiesCongruences

/-! ## 4 — Case analysis -/

namespace CaseAnalysis

-- 4.1
theorem ex1 (p q r : Prop) (h : p ∨ q) (hpr : p → r) (hqr : q → r) : r :=
  by
    rcases h with hp | hq
    · exact hpr hp
    · exact hqr hq

-- 4.2
theorem ex2 (n : ℕ) (h : n = 2 ∨ n = 4 ∨ n = 6) : n % 2 = 0 :=
  by rcases h with h | h | h <;> omega

-- 4.3
theorem ex3 : ¬∃ n : ℕ, 17 * n = 2 :=
  by
    push Not
    intro n
    rcases Nat.eq_zero_or_pos n with h | h
    · rw [h]
      norm_num
    · have : 17 * n ≥ 17 := by omega
      omega

-- 4.4
theorem ex4 (n : ℕ) : n ^ 2 - n = 0 ↔ n = 1 ∨ n = 0 :=
  by
    constructor
    · intro h
      obtain _ | _ | k := n
      · exact Or.inr rfl
      · exact Or.inl rfl
      · exfalso
        have h_le : (k + 2) ^ 2 ≤ k + 2 := Nat.sub_eq_zero_iff_le.mp h
        nlinarith
    · intro h
      obtain h1 | h0 := h
      · rw [h1]; norm_num
      · rw [h0]; norm_num

end CaseAnalysis

/-! ## 5 — Induction -/

namespace Induction

-- 5.1
theorem ex1 (n : ℕ) : 3 ^ n ≥ n + 1 :=
  by
    induction n with
    | zero => norm_num
    | succ k ih =>
      calc 3 ^ (k + 1)
          = 3 * 3 ^ k := by ring
        _ ≥ 3 * (k + 1) := by rel [ih]
        _ = (k + 1 + 1) + (2 * k + 1) := by ring
        _ ≥ k + 1 + 1 := by norm_num

-- 5.2
theorem ex2 (q : ℚ) (hq : 1 ≤ q) (n : ℕ) : 1 ≤ q ^ n :=
  by
    induction n with
    | zero => norm_num
    | succ k ih =>
      calc (1 : ℚ) = 1 * 1 := by ring
        _ ≤ q * q ^ k := by gcongr
        _ = q ^ (k + 1) := by ring

-- 5.3
-- Exercise 2, with `Nat.twoStepInduction`, gives two hypotheses in the step
-- case: the statement at `k` and at `k + 1`. That is exactly what the defining
-- equation of `v` consumes, since it reaches back a fixed distance of two.
-- Strong induction would also work, but nothing in the proof uses the cases
-- below `k`, so the extra strength is not needed.
--
-- Exercise 3, with `Nat.strong_induction_on`, gives `ih : ∀ m, m < n → P m`.
-- The proof applies it at `j`, which is half of `n`. That distance grows with
-- `n`, so no fixed number of hypotheses covers it: two hypotheses would supply
-- the statement at `n - 1` and `n - 2`, and for `n = 100` the proof needs it at
-- `50`.

end Induction

/-! ## 6 — Stronger tactics -/

namespace StrongerTactics

-- 6.1
theorem ex1 (x y : ℕ) (h : y = 0) : x + y + 0 = x :=
  by simp only [h, Nat.add_zero]

-- 6.2
theorem ex2 (a b : ℝ) : a * b ≤ (a ^ 2 + b ^ 2) / 2 :=
  by nlinarith [sq_nonneg (a - b)]

-- 6.3
-- The tactic `nlinarith` adds the non-negativity of the squares that occur in
-- the problem, and products of pairs of hypotheses. The square that is needed
-- is of `x - 1`, which does not occur in the statement, so the tactic does not
-- find the proof until the squares are supplied by hand.
theorem ex3 (x : ℝ) : x ^ 4 + 1 ≥ x ^ 3 + x :=
  by nlinarith [sq_nonneg (x - 1), sq_nonneg (x + 1), sq_nonneg x]

-- 6.4
theorem ex4 (p q r : Prop) (hpq : p → q) (hqr : q → r) : p → r :=
  by aesop

-- 6.5
theorem ex4_by_hand (p q r : Prop) (hpq : p → q) (hqr : q → r) : p → r :=
  fun hp => hqr (hpq hp)

#print axioms ex4          -- depends on axioms: [propext]
#print axioms ex4_by_hand  -- does not depend on any axioms

-- The two proofs prove the same statement and rest on different things. The
-- statement needs no axiom at all, as the term shows. The dependency reported
-- for `ex4` comes from the *proof `aesop` found*: the tactic normalises with
-- Mathlib's simp set, and the lemmas it used are stated using propositional
-- extensionality, so the term it built inherits `propext`.
--
-- The axiom `propext` is not classical: nothing here uses excluded middle, and
-- `Classical.choice` does not appear. The axioms a proof depends on are a
-- property of the proof term, not of the statement or of the tactic name.

end StrongerTactics

/-! ## 7 — Combinators and macros -/

namespace CombinatorsMacros

inductive Even : ℕ → Prop where
  | zero : Even 0
  | add_two : ∀ k : ℕ, Even k → Even (k + 2)

-- 7.1
theorem ex1 : Even 4 ∧ Even 6 ∧ Even 8 :=
  by
    repeat' apply And.intro
    all_goals
      repeat'
        first
        | apply Even.add_two
        | apply Even.zero

-- 7.2
namespace Ex2
macro "ℚ³" : term => `(ℚ × ℚ × ℚ)

def triple : ℚ³ := (1, 2, 3)
#check triple
end Ex2

-- 7.3
namespace Ex3
-- named `qdist`, not `dist`: Mathlib's `dist` is already defined on `ℚ`
def qdist (x y : ℚ) : ℚ := |x - y|

infixl:65 " ⊖ " => qdist

example (a b : ℚ) : a ⊖ b = b ⊖ a :=
  by
    unfold qdist
    rw [abs_sub_comm]
end Ex3

end CombinatorsMacros
