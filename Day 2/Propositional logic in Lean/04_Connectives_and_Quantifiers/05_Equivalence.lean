/-
Copyright (c) 2026 Iulian Simion. All rights reserved.
Released under the 3-Clause BSD License as described in the file LICENSE.txt.
Authors: Iulian Simion
-/
import Mathlib.Tactic.Linarith

/-
  # Equivalence Connective

  Given propositions `p` and `q`,
  the equivalence connective, `↔`, constructs the proposition `p ↔ q`,
  the witness of which consists of the juxtaposition of `h₁ : p → q` and `h₂ : q → p`.

  Similar to `∧`, the equivalence type `↔` is modeled as a *structure* depending on two propositions,
  since a proof-term for `p ↔ q` is instantiated by providing two fields:
  - modus ponens `: p → q` and
  - modus ponens reverse `: q → p`.
-/

section

#print Iff
#check Iff

variable (p q : Prop)
#check Iff p q    -- this is the proposition p ↔ q

#check Iff.intro  -- introduction rule
#check Iff.mp     -- elimination rule (modus ponens)
#check Iff.mpr    -- elimination rule (modus ponens reverse)

end

/-
  ## Equivalence Connective in CONTEXT

  We *consume* an equivalence by making use of its two constituent witnesses:
  `Iff.mp` and `Iff.mpr`.

  We build a new equivalence in our context by invoking the constructor
  `Iff.intro`.

  Instead of invoking the constructor explicitly, we may use the anonymous constructor
  `⟨ ... ⟩`,
  which works whenever the type of term we are constructing has exactly one constructor.
  However, since the constructor is anonymous, Lean needs to be able to infer
  that we are constructing an equivalence — below we need to specify the type explicitly.
-/

example (p q r : Prop) (h : p ↔ q) : r :=
  by
    have hpq := Iff.mp h
    have hqp := Iff.mpr h
    sorry

-- or

example (p q r : Prop) (h : p ↔ q) : r :=
  by
    have hpq := h.mp
    have hqp := h.mpr
    sorry

-- or

example (p q r : Prop) (h : p ↔ q) : r :=
  by
    obtain ⟨hpq,hqp⟩ := h
    sorry

-- constructing in local context

example (p q r : Prop) (hpq : p → q) (hqp : q → p) : r :=
  by
    have h := Iff.intro hpq hqp
    sorry

/-
  ## Equivalence Connective in TARGET

  When proving `p ↔ q`, we *construct* a witness of this proposition
  by supplying the witnesses for `hpq : p → q` and `hqp : q → p` to the constructor of this structure.

  ### Forward Reasoning
-/

example (p q : Prop) (hpq : p → q) (hqp : q → p) : p ↔ q := Iff.intro hpq hqp

-- or

example (p q : Prop) (hpq : p → q) (hqp : q → p) : p ↔ q := ⟨ hpq , hqp ⟩


example (n m: Nat) (h : n = m) : n = 7 ↔ m = 7 := Iff.intro (by intro _; linarith) (by omega)

-- or

example (n m: Nat) (h : n = m) : n = 7 ↔ m = 7 := ⟨ by intro _; linarith , by omega ⟩

/-
  ### Backward Reasoning

  In general, constructing the two witnesses before bundling them with the constructor
  is less straightforward and requires intermediate steps.
  In such cases, it is much more comfortable to enter tactic mode and to work *backwards*.

  Instead of focusing on the goal `C ⊢ p ↔ q`, it is enough to prove `C ⊢ p → q` and `C ⊢ q → p`.

  In Lean, we do this by reducing the target `p ↔ q` via the constructor, either
   - with `apply Iff.intro` or
   - with the `constructor` tactic.
-/

example (p q : Prop) : p ↔ q :=
  by
    apply Iff.intro
    · sorry
    · sorry

example (p q : Prop) : p ↔ q :=
  by
    constructor
    · sorry
    · sorry

example (n m : Nat) (h : n = m) : n = 7 ↔ m = 7 :=
  by
    constructor
    · intro _
      linarith
    · intro _
      linarith

/-
  EXAMPLE
-/

example (n : Nat) : n ^ 2 - n = 0 ↔ n = 1 ∨ n = 0 :=
  by
    constructor
    · intro h
      sorry
    · intro h
      obtain h1 | h0 := h
      · rw [h1]
        norm_num
      · rw [h0]
        norm_num


example (n : Nat) (h : n ^ 2 - n = 0) : n = 1 ∨ n = 0 :=
  by
    match n with
    | 0 => exact Or.inr rfl
    | 1 => exact Or.inl rfl
    | k + 2 =>
      exfalso
      have h_le : (k + 2)^2 ≤ k + 2 := Nat.sub_eq_zero_iff_le.mp h
      nlinarith
