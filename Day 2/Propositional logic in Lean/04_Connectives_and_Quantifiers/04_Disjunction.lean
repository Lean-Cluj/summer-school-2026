/-
Copyright (c) 2026 Iulian Simion. All rights reserved.
Released under the 3-Clause BSD License as described in the file LICENSE.txt.
Authors: Iulian Simion
-/
import Mathlib.Tactic.Linarith

/-
  # OR Connective (Disjunction)

  Given propositions `p` and `q`,
  the connective OR, `∨`, constructs the proposition `p ∨ q`,
  which may be witnessed by a witness of either of the two propositions.

  As a type, `Or` is modeled as an inductive type and depends on two propositions,
  since a proof-term for `p ∨ q` is instantiated either by `hp : p` or by `hq : q`.
-/

section

#print Or
#check Or

variable (p q : Prop)
#check Or p q    -- this is the proposition p ∨ q

#check Or.inl   -- introduction rule (constructor 1)
#check Or.inr   -- introduction rule (constructor 2)
#check Or.elim  -- elimination rule

end

/-
  ## OR Connective in CONTEXT

  When we have a disjunction in the context
  ` ... h : p ∨ q ... ⊢ t`
  we need to prove the target `t` if `p` holds or if `q` holds.

  Thus, *consuming* a disjunction ("eliminating" it from the context)
  amounts to splitting the goal in two:
  Goal 1 : ` ... h : p ... ⊢ t` modeled as ` ... ⊢ p → t`
  Goal 2 : ` ... h : q ... ⊢ t` modeled as ` ... ⊢ q → t`
-/

example (p q t : Prop) (h : p ∨ q) : t :=
  by
    apply Or.elim h
    · sorry
    · sorry

-- or, functional programming style

example (p q t : Prop) (h : p ∨ q) : t := Or.elim h sorry sorry

-- or, using `rcases`

example (p q t : Prop) (h : p ∨ q) : t :=
  by
    rcases h with hp | hq
    · sorry
    · sorry

-- or, using `obtain`

example (p q t : Prop) (h : p ∨ q) : t :=
  by
    obtain hp | hq := h
    · sorry
    · sorry


/-
  On the other hand, if you need to *construct* a disjunction in the local context,
  you may use either of the two constructors `Or.inl` or `Or.inr`.
-/

example (p q r : Prop) (hp : p) : r :=
  by
    have h : p ∨ q := Or.inl hp
    sorry

/-
  ### First-Order Logic examples
-/

example (n : Nat) (h : n = 2 ∨ n = 3) : n ≤ 7 :=
  by
    apply Or.elim h
    · intro hn
      linarith
    · intro hn
      linarith

-- or

example (n : Nat) (h : n = 2 ∨ n = 3) : n ≤ 7 :=
  Or.elim h (fun _ => by linarith) (by intro _; linarith)

-- or

example (n : Nat) (h : n = 2 ∨ n = 3) : n ≤ 7 :=
  by
    obtain h | h := h
    · linarith
    · linarith

/-
  ## OR Connective in TARGET

  When we have to prove a disjunction
  ` ... ⊢ p ∨ q `
  we need to *construct* it. Thus, we will use one of the two constructors `Or.inl` or `Or.inr`.

  ### Forward Reasoning
-/

example (n : Nat) (h : n = 1) : n=2 ∨ n=1 := Or.inr h

/-
  ### Backward Reasoning

  In general, constructing the left-hand side or the right-hand side of a disjunction
  is less straightforward and requires intermediate steps.
  In such cases, it is much more comfortable to enter tactic mode and to work *backwards*.

  Instead of focusing on the goal `C ⊢ p ∨ q`, it is enough to prove `C ⊢ p` or `C ⊢ q`.

  In Lean, we do this by reducing the target `p ∨ q` via the constructors, either
   - with `apply Or.inr` or `apply Or.inl`, or
   - with the `left` or `right` tactics.
-/

example (p q : Prop) : p ∨ q :=
  by
    apply Or.inr
    sorry

-- or

example (p q : Prop) : p ∨ q :=
  by
    right
    sorry

/-
  ### First-Order Logic examples

  Invoking the constructor explicitly.
-/

example (x : Nat) (h : x = 2) : x ≥ 1 ∨ x ≤ 1 :=
  by
    apply Or.inl
    linarith

-- or, using the `left` tactic

example (x : Nat) (h : x = 2) : x ≥ 1 ∨ x ≤ 1 :=
  by
    left
    linarith


-- or, functional programming style

example (x : Nat) (h : x = 2) : x ≥ 1 ∨ x ≤ 1 :=
  Or.inl
  (Nat.le_trans
      (Nat.le.step Nat.le.refl)
      (Nat.le_of_eq (Eq.symm h))
      )


/-
  Example 1
-/

example (x : ℕ) (h : x = 2 ∨ x = 3) : x ≥ 1 ∨ x ≤ 1 :=
  by
    apply Or.elim h
    · intro hx
      apply Or.inl
      linarith
    · intro hx
      apply Or.inl
      linarith

-- similar but shorter with `obtain`, `left` and `right` tactics

example (x : ℕ) (h : x = 2 ∨ x = 3) : x ≥ 1 ∨ x ≤ 1 :=
  by
    obtain hx | hx := h
    · left
      linarith
    · left
      linarith

/-
  Example 2
-/

theorem Or_swap (a b : Prop) :
  a ∨ b → b ∨ a :=
  by
    intro h
    apply Or.elim h
    { intro ha
      exact Or.inr ha }
    { intro hb
      exact Or.inl hb }

/-
  Example 3
-/

theorem le_or_succ_le (n m : ℕ) : n ≤ m ∨ m + 1 ≤ n :=
  by
    have h := lt_trichotomy n m
    obtain h₁ | h₂ | h₃ := h
    · left
      apply le_of_lt h₁
    · left
      apply le_of_eq h₂
    · right
      linarith
