/-
Copyright (c) 2026 Iulian Simion. All rights reserved.
Released under the 3-Clause BSD License as described in the file LICENSE.txt.
Authors: Iulian Simion
-/
import Mathlib.Tactic.Linarith

/-
  # AND Connective (Conjunction)

  Given propositions `p` and `q`,
  the connective AND, `∧`, constructs the proposition `p ∧ q`,
  the witness of which consists of the juxtaposition of the witnesses of the two propositions.

  As a type, `∧` is modeled as a *structure* depending on two propositions
  since a proof-term for `p ∧ q` is instantiated by providing two fields `hp : p` and `hq : q`.
-/

section

#print And
#check And
variable (p q : Prop)
#check And p q    -- this is the proposition p ∧ q

#check And.intro  -- introduction rule
#check And.left   -- elimination rule
#check And.right  -- elimination rule

end

/-
  ### AND Connective in CONTEXT

  We *consume* a conjunction by making use of its two constituent witnesses:
  `And.left` and `And.right`

  We build a new conjunction in our context by invoking the constructor
  `And.intro`

  Instead of invoking the constructor explicitly, we may use the anonymous constructor
  `⟨ ... ⟩`
  which works whenever the type of term we are constructing has exactly one constructor.
  However, in this case, since the constructor is anonymous, Lean needs to be able to infer
  that we are constructing a conjunction; below we need to specify the type explicitly.
-/

example (p q t : Prop) (h : p ∧ q) : t :=
  by
    have hp := And.left h
    have hq := And.left h
    sorry

example (p q t : Prop) (hp : p) (hq : q) : t :=
  by
    have hpq := And.intro hp hq
    sorry

-- or

example (p q t : Prop) (hp : p) (hq : q) : t :=
  by
    have h : p ∧ q:= ⟨hp,hq⟩
    sorry

/-
  ## AND Connective in TARGET

  When proving `p ∧ q` we *construct* a witness of this proposition
  by supplying the witnesses for `hp : p` and `hq : q` to the constructor of this structure.

  ### Forward Reasoning

-/

example (p q : Prop) (hp : p) (hq : q) : p ∧ q := And.intro hp hq

-- or

example (p q : Prop) (hp : p) (hq : q) : p ∧ q := ⟨ hp , hq ⟩


example (n : Nat) (h : n = 2) : n > 1 ∧ n < 7 := And.intro (by linarith) (by linarith)

-- or

example (n : Nat) (h : n = 2) : n > 1 ∧ n < 7 := ⟨ by linarith , by linarith ⟩

/-
  ### Backward Reasoning

  In general, constructing the two witnesses before bundling them with the constructor
  is less straightforward and requires intermediate steps.
  In such cases it is much more comfortable to enter tactic mode and to work *backwards*.

  Instead of focusing on the goal `C ⊢ p ∧ q`, it is enough to prove two goals `C ⊢ p` and `C ⊢ q`.

  In Lean we do this by reducing the target `p ∧ q` via the constructor, either
   - with `apply And.intro` or
   - with the `constructor` tactic
-/

example (p q : Prop) (hp : p) (hq : q) : p ∧ q := by
  apply And.intro
  · apply hp
  · apply hq

example (p q : Prop) (hp : p) (hq : q) : p ∧ q := by
  constructor
  · apply hp
  · apply hq

#check ge_of_eq
example (n : Nat) (h : n = 5) : n ≥ 5 ∧ n ≤ 5 := by
  constructor
  · apply ge_of_eq h
  · apply le_of_eq h

/-
  EXAMPLE [Hitch 3.3]

  Let us consider the various ways in which we can produce a proof term
  for the commutativity of conjunction:
  `p ∧ q → q ∧ p`
-/

theorem And_swap (p q : Prop) :  p ∧ q → q ∧ p :=
  by
    intro h
    apply And.intro
    · apply And.right
      exact h
    apply And.left
    exact h

-- Similar but with variables expressed with the universal quantifier:

theorem And_swap_braces :
  ∀ p q : Prop, p ∧ q → q ∧ p :=
  by
    intro p q h
    apply And.intro
    { exact And.right h }
    { exact And.left h }

-- Using the anonymous constructor:

theorem And_swap_have :
  ∀ p q : Prop, p ∧ q → q ∧ p :=
  by
    intro p q h
    have ⟨hp,hq⟩ := h
    exact ⟨hq,hp⟩

-- This is a forward reasoning approach (functional programming style):

theorem And_swap_functional :
  ∀ p q : Prop, p ∧ q → q ∧ p :=
  fun _ _ h => ⟨h.right,h.left⟩
