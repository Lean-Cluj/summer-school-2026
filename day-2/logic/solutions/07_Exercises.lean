/-
Copyright (c) 2026 Iulian Simion. All rights reserved.
Released under the 3-Clause BSD License as described in the file LICENSE.
Authors: Iulian Simion, assisted by Claude (Anthropic) and Gemini (Google)
-/
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Push
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.Contrapose
import Mathlib.Tactic.Tauto

/-! # Solutions — Further exercises for the morning -/

/-! ## 1 — Propositions -/

namespace Propositions

-- 1.1
#check (5 * 5 = 25)
#check (5 * 5 = 26)

-- 1.2
-- All three work, for three different reasons: `rfl` because both sides
-- reduce to `7`, `decide` because equality on `ℕ` is decidable and the
-- procedure returns "true", and `Nat.add_zero 7` because it is a lemma whose
-- statement is exactly this equation.
theorem ex2 : (7 : Nat) + 0 = 7 := rfl
example : (7 : Nat) + 0 = 7 := by decide
example : (7 : Nat) + 0 = 7 := Nat.add_zero 7

-- 1.3
#print ex2
-- With `rfl` the term is just `rfl`. Proved `by decide` instead, the same
-- statement gets the term `of_decide_eq_true (id (Eq.refl true))`: the
-- decision procedure was run, and it returned `true`. With the lemma the term
-- is `Nat.add_zero 7`, a theorem applied to an argument like a function. The
-- statement is the same each time; the three proofs are different terms.

-- 1.4
theorem ex4 : True := True.intro

end Propositions

/-! ## 2 — Implication and the universal quantifier -/

namespace ImplicationUniversal

-- 2.1
theorem ex1 (p q : Prop) (hp : p) : (p → q) → q :=
  fun hpq => hpq hp

-- 2.2
theorem ex2 (p q r : Prop) : (p → q → r) → (p → q) → p → r :=
  fun hpqr hpq hp => hpqr hp (hpq hp)

-- 2.3
theorem ex3 (n : Nat) : n = 3 → n + 2 = 5 :=
  by
    intro h
    linarith

-- 2.4
theorem ex4 (n m : Nat) : n ≤ m → n + 1 ≤ m + 1 :=
  fun h => Nat.succ_le_succ h

theorem ex4' (n m : Nat) : n ≤ m → n + 1 ≤ m + 1 :=
  by
    intro h
    linarith

-- 2.5
theorem ex5 : ∀ x : Nat, x * 0 = 0 :=
  by
    intro x
    rfl

-- 2.6
theorem ex6 (f : Nat → Nat) (h : ∀ n : Nat, f n = n) : f 3 = 3 :=
  h 3

-- 2.7
theorem ex7 : ∀ p q : Prop, p → q → p :=
  fun _ _ hp _ => hp

end ImplicationUniversal

/-! ## 3 — Conjunction, disjunction, equivalence -/

namespace ConjunctionDisjunction

-- 3.1
theorem ex1 (p q r : Prop) (h : p ∧ (q ∧ r)) : (p ∧ q) ∧ r :=
  ⟨⟨h.left, h.right.left⟩, h.right.right⟩

-- the same, in tactic mode, as the exercise also asks
example (p q r : Prop) (h : p ∧ (q ∧ r)) : (p ∧ q) ∧ r :=
  by
    obtain ⟨hp, hq, hr⟩ := h
    constructor
    · constructor
      · exact hp
      · exact hq
    · exact hr

-- 3.2
theorem ex2 (p q r : Prop) (h : p ∧ q) (hpr : p → r) : r ∧ q :=
  by
    obtain ⟨hp, hq⟩ := h
    exact ⟨hpr hp, hq⟩

-- 3.3
theorem ex3 (n : Nat) (h : n = 0 ∨ n = 1) : n ≤ 1 :=
  by
    obtain h0 | h1 := h
    · linarith
    · linarith

-- 3.4
theorem ex4 (p q r : Prop) : (p ∨ q) ∨ r → p ∨ (q ∨ r) :=
  by
    intro h
    obtain hpq | hr := h
    · obtain hp | hq := hpq
      · left
        exact hp
      · right
        left
        exact hq
    · right
      right
      exact hr

-- 3.5
theorem ex5 (n : Nat) : n = 0 ∨ 0 < n :=
  Nat.eq_zero_or_pos n

-- 3.6
theorem ex6 (p : Prop) : p ↔ p :=
  ⟨fun hp => hp, fun hp => hp⟩

-- Built by hand above, as the exercise asks. The library already has it:
example (p : Prop) : p ↔ p := Iff.rfl

-- 3.7
theorem ex7 (p q : Prop) : (p ∧ q) ↔ (q ∧ p) :=
  by
    constructor
    · intro h
      exact ⟨h.right, h.left⟩
    · intro h
      exact ⟨h.right, h.left⟩

-- 3.8
theorem ex8 (n : Nat) : n + 1 = 1 ↔ n = 0 :=
  by
    constructor
    · intro h
      omega
    · intro h
      omega

end ConjunctionDisjunction

/-! ## 4 — The existential quantifier, and negation -/

namespace ExistentialNegation

-- 4.1
theorem ex1 : ∃ n : Nat, n * n = 49 :=
  by
    use 7

-- 4.2
-- The witness `0` is available because `Nat` is known to have an element. For
-- an arbitrary type `α` the statement fails exactly when `α` is empty: then
-- `∀ n, p n` holds vacuously while `∃ n, p n` has no witness to offer.
theorem ex2 (p : Nat → Prop) (h : ∀ n, p n) : ∃ n, p n :=
  ⟨0, h 0⟩

-- 4.3
theorem ex3 : ∃ x : ℝ, 1 < x ∧ x < 2 :=
  by
    use 3 / 2
    norm_num

-- 4.4
theorem ex4 (p : Prop) (hp : p) : ¬¬p :=
  fun hnp => hnp hp

-- 4.5
theorem ex5 (p q : Prop) (hpq : p → q) : ¬q → ¬p :=
  by
    intro hnq hp
    exact hnq (hpq hp)

-- 4.6
theorem ex6 (n : Nat) (h : n = 5) : n ≠ 6 :=
  by omega

-- 4.7
theorem ex7 (p q : Prop) : ¬(p ∨ q) → ¬p ∧ ¬q :=
  by
    intro h
    constructor
    · intro hp
      exact h (Or.inl hp)
    · intro hq
      exact h (Or.inr hq)

-- 4.8
theorem ex8 (h : ¬∃ x : Nat, x > 3) : ∀ x : Nat, x ≤ 3 :=
  by
    push Not at h
    exact h

end ExistentialNegation

/-! ## 5 — Classical logic -/

namespace ClassicalLogic

-- 5.1
theorem not_forall_iff (p : ℕ → Prop) : (¬∀ n, p n) ↔ ∃ n, ¬ p n :=
  by
    constructor
    · intro h
      push Not at h
      exact h
    · intro h hall
      obtain ⟨n, hn⟩ := h
      exact hn (hall n)

#print axioms not_forall_iff

-- 5.2
theorem constructive_half (p : Prop) : p → ¬¬p :=
  fun hp hnp => hnp hp

#print axioms constructive_half

end ClassicalLogic

/-! ## 6 — `Prop` and `Bool` -/

namespace PropBool

-- 6.1
#eval decide (5 * 5 = 25)
#eval decide (5 < 3)
#eval decide (2 ∣ 10)

-- 6.2
theorem ex2 : (13 : ℕ) ∣ 169 := by decide

end PropBool
