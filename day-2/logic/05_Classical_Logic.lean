/-
Copyright (c) 2026 Iulian Simion. All rights reserved.
Released under the 3-Clause BSD License as described in the file LICENSE.
Authors: Iulian Simion, assisted by Claude (Anthropic) and Gemini (Google)
-/
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.Choose
import Mathlib.Tactic.Contrapose
import Mathlib.Tactic.Tauto
import Mathlib.Tactic.Push

/-!
# Classical logic

A proof is constructive when it proves a disjunction by proving one of its
sides, and an existential statement by producing a witness. The rules of CIC
are constructive in this sense. Classical logic adds principles that are not,
and in Lean they are available because they follow from axioms the system
assumes.

The command `#print axioms` lists the axioms a declaration depends on. A proof
that stays within the rules reports none.
-/

theorem not_not_not_elim (p : Prop) : ¬¬¬p → ¬p :=
  by
    intro h hp
    exact h (fun k => k hp)

#print axioms not_not_not_elim

/-!
The dependency is traced through the whole proof, so a proof with no visible
classical step still reports the axioms when a tactic or a library lemma it
uses depends on them. The tactic `linarith` is classical in this way.

# The law of excluded middle

For every proposition `p`, either `p` holds or `¬p` holds.
-/

#check @Classical.em

/-!
This is not provable from the introduction and elimination rules. A proof of a
disjunction is a proof of one of its sides, and for an arbitrary `p` neither
side can be produced. Excluded middle supplies a proof of `p ∨ ¬p` all the
same, without determining which side holds.

The term `Classical.em p` proves an ordinary disjunction, so `obtain` splits it
into two cases exactly as in `04`. The effect is a case analysis on a
proposition, available for any `p` whatever.
-/

theorem cases_on_a_proposition (p q : Prop) (h₁ : p → q) (h₂ : ¬p → q) : q :=
  by
    obtain hp | hnp := Classical.em p
    · exact h₁ hp
    · exact h₂ hnp

#print axioms cases_on_a_proposition

/-!
## `by_cases`

The tactic `by_cases hp : p` performs that split directly. It produces two
goals, one with `hp : p` and one with `hp : ¬p`, and leaves the target
unchanged in both.
-/

theorem by_cases_example (p q : Prop) (h₁ : p → q) (h₂ : ¬p → q) : q :=
  by
    by_cases hp : p
    · exact h₁ hp
    · exact h₂ hp

#print axioms by_cases_example

/-!
When the proposition is decidable, the tactic uses its decision procedure
instead of the axiom, and the proof reports nothing.
-/

theorem by_cases_decidable (n : Nat) : n = 0 ∨ n ≠ 0 :=
  by
    by_cases h : n = 0
    · exact Or.inl h
    · exact Or.inr h

#print axioms by_cases_decidable

/-!
## `by_contra`

To prove `p`, the tactic `by_contra hnp` assumes `hnp : ¬p` and replaces the
target by `False`.
-/

theorem dne (p : Prop) (h : ¬¬p) : p :=
  by
    by_contra hnp   -- hnp : ¬p, target : False
    exact h hnp

#print axioms dne

/-!
Proving `¬p` by assuming `p` and deriving `False` is constructive, since that
is the definition of `¬`. Concluding `p` from `¬¬p` is the step that needs the
axiom.

The two tactics differ in shape: `by_contra hnp` adds **one** hypothesis and
changes the target to `False`; `by_cases hp : p` produces **two** goals and
leaves the target alone.

## `contrapose`

The tactic replaces the target `p → q` by `¬q → ¬p`.
-/

theorem contrapose_example (p q : Prop) (h : ¬q → ¬p) : p → q :=
  by
    contrapose
    exact h

#print axioms contrapose_example

/-!
Here too, one direction is constructive and the other is not: from `p → q` the
implication `¬q → ¬p` follows by the rules alone, while recovering `p → q`
from `¬q → ¬p` needs double negation elimination.

## `push Not` past a `∀`

Not every rule of `push Not` is constructive. Turning `¬∀ x, P x` into
`∃ x, ¬ P x` is not: it asserts a witness that no proof has produced.
-/

theorem push_not_forall (P : ℕ → Prop) (h : ¬∀ x, P x) : ∃ x, ¬ P x :=
  by
    push Not at h
    exact h

#print axioms push_not_forall

/-!
## `tauto`

The tactic `tauto` settles goals that follow from propositional structure
alone, and it uses classical rules to do so. Peirce's law is an example: a
tautology of classical propositional logic with no constructive proof.
-/

theorem peirce_law (p q : Prop) : ((p → q) → p) → p :=
  by tauto

#print axioms peirce_law

/-!
## The same principle in several forms

Four statements are traditionally singled out. Over the constructive rules,
they are equivalent to one another, so assuming any one of them yields the
rest.

* *tertium non datur*, excluded middle: `∀ p, p ∨ ¬p`
* *duplex negatio affirmat*, double negation elimination: `∀ p, ¬¬p → p`
* *reductio ad absurdum*, proof by contradiction: `∀ p, (¬p → False) → p`
* Peirce's law: `∀ p q, ((p → q) → p) → p`

The middle two are not merely equivalent but the same statement. Since `¬p` is
*defined* as `p → False`, `¬¬p` is `(p → False) → False`, which is `¬p → False`.
The two sides are the same proposition after unfolding, so `Iff.rfl` proves the
equivalence and no axiom is involved.
-/

theorem pbc_iff_dne : (∀ p : Prop, (¬p → False) → p) ↔ (∀ p : Prop, ¬¬p → p) :=
  Iff.rfl

#print axioms pbc_iff_dne

/-!
Excluded middle is a different statement, and its equivalence with double
negation elimination has to be proved. The tactic `tauto` finds a proof.
-/

theorem em_iff_dne : (∀ p : Prop, p ∨ ¬p) ↔ (∀ p : Prop, ¬¬p → p) :=
  by tauto

#print axioms em_iff_dne

/-!
The proof `tauto` produces is itself classical, as its axioms show. A
constructive proof of the same equivalence exists, and exercise 2 asks for it:
showing that two classical principles are interderivable need not use either
of them.

# The axiom of choice

Excluded middle is a theorem in Lean, not an axiom. What Lean assumes is the
axiom of choice, which supplies an element of a type from the knowledge that
the type is non-empty.
-/

#check @Classical.choice

/-!
The constant `Classical.choice` is declared with the keyword `axiom`: it is
assumed, not proved. It produces an element with no procedure for computing it,
which is why a definition that uses it must be marked `noncomputable`.

Excluded middle is derived from it by **Diaconescu's theorem**, which needs
choice together with propositional and function extensionality. Three axioms
therefore appear when `Classical.em` is traced:

* `Classical.choice`, the axiom of choice;
* `propext`, propositional extensionality: propositions that imply each other
  are equal;
* `Quot.sound`, the rule behind quotient types, from which function
  extensionality follows.
-/

#print axioms Classical.em

/-!
Lean core gathers the classical primitives, among them `choice`, `em`,
`byContradiction` and `propDecidable`, in the `Classical` namespace. Only
declarations *stated* there live in it; most results that *depend* on
`Classical.choice` do not, and the theorems above sit in the root namespace.
Whether a proof is classical cannot be read off a name, and `#print axioms`
is what settles it.

## `choose`

If for every `x` there is some `y` with `R x y`, then there is a function
picking such a `y` for each `x`. Passing from the first statement to the second
is an application of choice, and `choose` is the tactic that applies it. It is
the one tool in this file that uses choice and nothing else.
-/

theorem choose_example {α β : Type} (R : α → β → Prop) (h : ∀ x, ∃ y, R x y) :
    ∃ f : α → β, ∀ x, R x (f x) :=
  by
    choose f hf using h   -- f : α → β,  hf : ∀ x, R x (f x)
    exact ⟨f, hf⟩

#print axioms choose_example

/-!
## `classical`

An expression `if p then _ else _` needs a way to evaluate `p`, which Lean
records as an instance of `Decidable p`. For an arbitrary proposition, there is
no such procedure. The `classical` tactic supplies the instance anyway, using
excluded middle, and the definition has to be marked `noncomputable` since
there is nothing to run.
-/

noncomputable def indicator (p : Prop) : Nat :=
  by
    classical
    exact if p then 1 else 0

#print axioms indicator

/-!
## Classical logic in Mathlib

Mathlib uses excluded middle and the axiom of choice freely, and most of its
theorems depend on `Classical.choice`. The tactics of this file are used there
just as freely, and `#print axioms` shows where the axioms enter. A constructive
proof of an existential statement yields a way to compute the witness; a
classical proof need not.

# Exercises

Solutions: `solutions/05_Classical_Logic.lean`. Further exercises: section 5 of
`07_Exercises.lean`.
-/

/-! ## 1 — one of the two De Morgan laws
This one is constructive in *both* directions: no classical tactic is needed.
(The other De Morgan law, `¬(p ∧ q) → ¬p ∨ ¬q`, is the one with no
constructive proof.) -/

theorem de_morgan (p q : Prop) : ¬(p ∨ q) → ¬p ∧ ¬q := sorry

#print axioms de_morgan

/-! ## 2 — double negation elimination is equivalent to excluded middle

*Left to right.* Assume `hdne : ∀ p, ¬¬p → p` and let `p` be given. Apply
`hdne` to the goal `p ∨ ¬p`, which leaves you to derive `False` from
`hn : ¬(p ∨ ¬p)`. Exercise 1 turns `hn` into `¬p ∧ ¬¬p`, which is a
contradiction.

*Right to left.* Assume excluded middle for `p` and split on it.

Neither direction needs any tactic beyond `constructor`, `intro`, `apply`,
`obtain` and `exact` — `constructor` to split the `↔`, and again for the `∧`
in exercise 1. -/

theorem dne_iff_lem : (∀ p : Prop, ¬¬p → p) ↔ (∀ p : Prop, p ∨ ¬p) := sorry

#print axioms dne_iff_lem

/-! ## 3 — the classical direction of the contrapositive
The tactic is `by_contra`. -/

theorem contrapositive (p q : Prop) : (¬q → ¬p) → (p → q) := sorry

#print axioms contrapositive
