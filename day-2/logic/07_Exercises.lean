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

/-!
# Further exercises for the morning

Further exercises on the morning's topics, one section per topic file
`01`–`06`, each inside its own `namespace`. No section depends on another.

Replace every `sorry` by a proof. Exercises 1.1, 1.3 and 6.1 are commented-out
commands to be completed.

Solutions: `solutions/07_Exercises.lean`.
-/

/-! ## 1 — Propositions

After `01_Propositions.lean`. -/

namespace Propositions

/-! ### 1.1
Write two `#check` commands, one for a true proposition about numbers and one
for a false one. Confirm in the Infoview that both have type `Prop`. -/

-- #check …
-- #check …

/-! ### 1.2
Prove `(7 : Nat) + 0 = 7`. Which of `rfl`, `decide` and `Nat.add_zero 7` work
here? Try all three, and say what each one is doing. -/

theorem ex2 : (7 : Nat) + 0 = 7 := sorry

/-! ### 1.3
Use `#print` to look at the proof term Lean built for `ex2`, the theorem of
exercise 1.2. Then replace that proof by each of the other two that work, and
look again. -/

-- #print ex2

/-! ### 1.4
The term `True.intro` is the proof of `True`. Use it. -/

theorem ex4 : True := sorry

end Propositions

/-! ## 2 — Implication and the universal quantifier

After `02_Implication_and_Universal.lean`. -/

namespace ImplicationUniversal

/-! ### 2.1 — modus ponens
Prove it as a *term*: no `by`. -/

theorem ex1 (p q : Prop) (hp : p) : (p → q) → q := sorry

/-! ### 2.2 — the same hypothesis used twice
Prove it as a term. -/

theorem ex2 (p q r : Prop) : (p → q → r) → (p → q) → p → r := sorry

/-! ### 2.3 — a concrete implication
Introduce the hypothesis, then let `linarith` finish. -/

theorem ex3 (n : Nat) : n = 3 → n + 2 = 5 := sorry

/-! ### 2.4 — twice over
Prove the same statement two ways: once as a term using `Nat.succ_le_succ`,
once in tactic mode using `linarith`. -/

theorem ex4 (n m : Nat) : n ≤ m → n + 1 ≤ m + 1 := sorry

theorem ex4' (n m : Nat) : n ≤ m → n + 1 ≤ m + 1 := sorry

/-! ### 2.5 — a `∀` in tactic mode
Exercise 2 of `02_Implication_and_Universal.lean` proved a `∀` as a term. Prove this one in the other style: `intro` first. -/

theorem ex5 : ∀ x : Nat, x * 0 = 0 := sorry

/-! ### 2.6 — specialising a hypothesis about a function -/

theorem ex6 (f : Nat → Nat) (h : ∀ n : Nat, f n = n) : f 3 = 3 := sorry

/-! ### 2.7 — four arguments
Only one of them is used. -/

theorem ex7 : ∀ p q : Prop, p → q → p := sorry

end ImplicationUniversal

/-! ## 3 — Conjunction, disjunction, equivalence

After `03_Conjunction_Disjunction_Equivalence.lean`. -/

namespace ConjunctionDisjunction

/-! ### 3.1 — regrouping a conjunction
Conjunction associates to the right, so `p ∧ q ∧ r` *would* mean
`p ∧ (q ∧ r)`. Here, the brackets are written out on both sides. Nothing is
lost, but they have to be rebuilt.

Try it as a term with `⟨…, …⟩`, and then again in tactic mode. -/

theorem ex1 (p q r : Prop) (h : p ∧ (q ∧ r)) : (p ∧ q) ∧ r := sorry

/-! ### 3.2 — destructure, transform, rebuild
Use `obtain ⟨hp, hq⟩ := h`. -/

theorem ex2 (p q r : Prop) (h : p ∧ q) (hpr : p → r) : r ∧ q := sorry

/-! ### 3.3 — a concrete disjunction in the context -/

theorem ex3 (n : Nat) (h : n = 0 ∨ n = 1) : n ≤ 1 := sorry

/-! ### 3.4 — reassociating a disjunction
The incoming disjunction is nested, so getting its three cases takes two
`obtain`s. -/

theorem ex4 (p q r : Prop) : (p ∨ q) ∨ r → p ∨ (q ∨ r) := sorry

/-! ### 3.5 — from the library
Every natural number is zero or positive. Prove it with the library lemma
`Nat.eq_zero_or_pos`. -/

theorem ex5 (n : Nat) : n = 0 ∨ 0 < n := sorry

/-! ### 3.6 — the simplest equivalence, as a term -/

theorem ex6 (p : Prop) : p ↔ p := sorry

/-! ### 3.7 — commutativity of conjunction, as an equivalence
Both directions have the same proof. -/

theorem ex7 (p q : Prop) : (p ∧ q) ↔ (q ∧ p) := sorry

/-! ### 3.8 — a concrete equivalence
Split with `constructor`, then `intro`, then `omega` in each branch. -/

theorem ex8 (n : Nat) : n + 1 = 1 ↔ n = 0 := sorry

end ConjunctionDisjunction

/-! ## 4 — The existential quantifier, and negation

After `04_Existential_and_Negation.lean`. -/

namespace ExistentialNegation

/-! ### 4.1 — a witness you have to think about -/

theorem ex1 : ∃ n : Nat, n * n = 49 := sorry

/-! ### 4.2 — from `∀` to `∃`
This needs a witness, so you must pick a particular natural number. Why does
the same statement fail for an arbitrary type `α` in place of `Nat`? -/

theorem ex2 (p : Nat → Prop) (h : ∀ n, p n) : ∃ n, p n := sorry

/-! ### 4.3 — over the reals
Pick a rational witness and let `norm_num` check the two inequalities. -/

theorem ex3 : ∃ x : ℝ, 1 < x ∧ x < 2 := sorry

/-! ### 4.4 — introducing a double negation, as a term
Recall that `¬¬p` is `(p → False) → False`, so the term is a function. -/

theorem ex4 (p : Prop) (hp : p) : ¬¬p := sorry

/-! ### 4.5 — the contrapositive
This direction needs no classical logic. -/

theorem ex5 (p q : Prop) (hpq : p → q) : ¬q → ¬p := sorry

/-! ### 4.6 — a concrete inequation -/

theorem ex6 (n : Nat) (h : n = 5) : n ≠ 6 := sorry

/-! ### 4.7 — one of the two De Morgan laws
Split the goal with `constructor`. Each half assumes something and must
produce `False`, which `h` will give you once you feed it a disjunction. -/

theorem ex7 (p q : Prop) : ¬(p ∨ q) → ¬p ∧ ¬q := sorry

/-! ### 4.8 — pushing a negation past `∃`
Two steps: `push Not at h`, then use the rewritten hypothesis.

Pushing a negation past `∀` rather than `∃` is classical; see exercise 5.1. -/

theorem ex8 (h : ¬∃ x : Nat, x > 3) : ∀ x : Nat, x ≤ 3 := sorry

end ExistentialNegation

/-! ## 5 — Classical logic

After `05_Classical_Logic.lean`. Run `#print axioms` on each theorem when you
are done, and do not use `tauto`. One of the two is constructive. -/

namespace ClassicalLogic

/-! ### 5.1 — negating a `∀`
One direction is `push Not`; the other you should do by hand. Which of the
two is the classical one? -/

theorem not_forall_iff (p : ℕ → Prop) : (¬∀ n, p n) ↔ ∃ n, ¬ p n := sorry

#print axioms not_forall_iff

/-! ### 5.2 — for contrast
Prove this one as a term and confirm with `#print axioms` that it needs
nothing. -/

theorem constructive_half (p : Prop) : p → ¬¬p := sorry

#print axioms constructive_half

end ClassicalLogic

/-! ## 6 — `Prop` and `Bool`

After `06_Prop_vs_Bool.lean`. -/

namespace PropBool

/-! ### 6.1 — evaluate some decisions
Write three `#eval decide (…)` lines and predict each answer before looking. -/

-- #eval decide (…)

/-! ### 6.2 — a divisibility statement -/

theorem ex2 : (13 : ℕ) ∣ 169 := sorry

end PropBool
