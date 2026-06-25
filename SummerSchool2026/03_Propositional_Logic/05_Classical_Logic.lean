/-
Copyright (c) 2026 Iulian Simion. All rights reserved.
Released under the 3-Clause BSD License as described in the file LICENSE.txt.
Authors: Iulian Simion

Note: Parts of this file were synthesized with the assistance of Gemini 3.1 Pro.
-/
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.Choose
import Mathlib.Tactic.Contrapose
import Mathlib.Tactic.Tauto
import Aesop
/-
  # Law of excluded middle (LEM)

  The law of excluded middle states that for any proposition `p`,
  either `p` is true, or `¬p` is true.

  Notice that the law guarantees a proof term for `p ∨ ¬ p`
  whithout having produced such a proof term.

  The above proposition cannot be proved with standard Lean.
-/
example (p : Prop) : p ∨ ¬ p :=
  sorry

#check Classical.em

/-
  # Axiom of choice (AC)

  The Law of excluded middle is an effect of the Axiom of choice.

  From Prelude.lean:
    `Nonempty α` is a proof that `α` has an element, but the element itself is erased.
    The axiom `choice` supplies a particular element of `α` given only this proof.

    This axiom can be used to construct "data", but obviously there is no algorithm
    to compute it, so Lean will require you to mark any definition that would
    involve executing `Classical.choice` or other axioms as `noncomputable`, and
    will not produce any executable code for such definitions.

  The implementation `Classical.em` of LEM follows Diaconescu's Theorem,
  which states that AC implies LEM.

  `Classical.choice` is modeled via `axiom`.
-/
#check Classical.choice

/-
  Since AC and LEM are comonly used by mathematicians,
  The namespace `Classical` is a "quarantine zone" for non-constructive mathematics.

  It makes classical reasoning tools possible and it extends other tools.


  ### choose (Extracting a function)

  When you know every `x` has some `y` that satisfies a relation,
  `choose` magically materializes a function `f` that picks that `y` for you.

-/

example {α β : Type} (R : α → β → Prop) (h : ∀ x, ∃ y, R x y) :
    ∃ f : α → β, ∀ x, R x (f x) := by
  -- Extracts a choice function `f` and the proof it works `hf`
  choose f hf using h
  exact ⟨f, hf⟩

/-
  ### by_contra (Proof by Contradiction)

  Proving `p` by assuming `¬ p` and deriving a contradiction.
  This is the classic way to prove double negation elimination.

-/
example (p : Prop) (h : ¬¬p) : p := by
  -- "Assume ¬p to derive a contradiction"
  by_contra h_not_p
  -- Now we have h_not_p : ¬p, and h : ¬¬p
  exact h h_not_p

/-
  ### contrapose (Contrapositive of the goal)

  Swapping the direction of an implication.
  Going from `p → q` to `¬ q → ¬ p` is constructive,
  but the reverse relies on classical logic.
-/
example (p q : Prop) (h : ¬q → ¬p) : p → q := by
  -- Transforms the goal `p → q` into `¬q → ¬p`
  contrapose
  exact h

/-
  ### classical (Faking Decidability)

  Using `classical` allows you to write computational structures (like `if-then-else`)
  on abstract propositions that Lean doesn't know how to evaluate.
  Because there's no real algorithm, you must mark the definition `noncomputable`.

-/
-- p is entirely abstract; Lean has no way to compute if it's true
noncomputable def indicator (p : Prop) : Nat := by
  -- Forces Lean to pretend p is Decidable
  classical
  exact if p then 1 else 0

/-
  ### by_cases (Branching on Excluded Middle)

  Splitting a proof into a case where `p` is true and a case where `p` is false,
  without knowing which it is.

-/
example (p q : Prop) (h1 : p → q) (h2 : ¬p → q) : q := by
  -- Splits into two subgoals: `hp : p` and `hnp : ¬p`
  by_cases hp : p
  · exact h1 hp
  · exact h2 hp

/-
  ### push_neg (Pushing negations inward)

  Turning `¬ ∀ x, p(x)` into `∃ x, ¬ p(x)`.
  This requires classical logic to bridge the gap between
  "not everything is true" and "something specific is false."

-/
example (P : Nat → Prop) (h : ¬ ∀ x, P x) : ∃ x, ¬ P x := by
  -- Pushes the negation through the universal quantifier
  push Not at h
  exact h

/-
  ### tauto (Propositional Tautologies)

  `tauto` automatically solves logic problems using classical rules.
  Here it solves Peirce's Law,
  a statement that is notoriously impossible to prove in pure constructive logic.
-/
example (p q : Prop) : ((p → q) → p) → p := by
  -- Closes the goal automatically using classical logic
  tauto


/-
  ### aesop (Automated Proof Search)

  `aesop` is a powerful search tree tactic.
  By default, it includes classical axioms in its search rules,
  meaning it will happily apply double negation or excluded middle
  if it helps close the goal.
-/
example (p q : Prop) (h : ¬p → ¬q) : q → p := by
  -- aesop figures out the classical contrapositive automatically
  aesop



/-
  EXERCISE:

  Show that the following are equivalent
    `tertium non datur` (Law of Excluded Middle)
    `duplex negatio affirmat` (Double Negation Elimination)
    `reductio ad absurdum` (Proof by Contradiction)
-/
theorem PBC_iff_DNE : (∀ p : Prop, (¬p → False ) → p) ↔ (∀ p : Prop, ¬¬p → p) :=
  by rfl

-- you may want to prove this intermediate result
theorem de_Morgan (p q : Prop) : ¬(p ∨ q) → ¬p ∧ ¬q :=
  sorry

theorem DNE_iff_LEM : (∀ p : Prop, ¬¬p → p) ↔ (∀ p : Prop, p ∨ ¬p) :=  sorry
