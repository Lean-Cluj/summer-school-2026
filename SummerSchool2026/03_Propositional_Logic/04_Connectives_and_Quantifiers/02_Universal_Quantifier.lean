/-
Copyright (c) 2026 Iulian Simion. All rights reserved.
Released under the 3-Clause BSD License as described in the file LICENSE.txt.
Authors: Iulian Simion
-/
import Mathlib.Tactic.Linarith

/-
  # Universal Quantifier

  The universal quantifier `∀` constructs propositions depending on other types.

  `∀ a : α, p(a)`

  It constructs the type of a function which
  *maps terms* `a : α` to *proof terms* of the proposition `p(a)`.
-/

section

variable (p : Nat → Prop)

#check (∀ n : Nat, p n)

#check ((n : Nat) → p n)

example : (∀ n : Nat, p n) = ((n : Nat) → p n) := rfl

end

/-
  ## Universal Quantifier in TARGET

  When proving `∀ a : α, p(a)` we *construct* a function `f` of type `a : α → p(a)`, i.e.
  `f(a) = witness of p(a)`

  ### Forward Reasoning (The raw functional programming way):
-/

example : ∀ a b : Nat, a + b = b + a :=
  fun a b : Nat => Nat.add_comm a b

example : ∀ p : Prop, p → p :=
  fun _ hp => hp

/-
  Notice the difference:
-/

#check (fun a b : ℕ => Nat.add_comm a b)
#check (fun a b : ℕ => a + b = b + a)

example : (∀ a b : ℕ, a + b = b + a) = ((a b : Nat) → a + b = b + a) :=
  rfl

/-
  ### Backward Reasoning (The tactic way):

  Since `∀ a : α, p(a)` is the same as `a : α → p(a)`
  and since we may prove implications by
  assuming the left hand side and showing the right hand side,
  we may also write
-/

example : ∀ a b : Nat, a + b = b + a :=
  by
    intro a b
    exact Nat.add_comm a b

example : ∀ p : Prop, p → p :=
  by
    intro _ hp
    exact hp

/-
  The `intro` tactic introduces the hypothesis into the context.
  It deconstructs the `→` operator and can be used in other contexts, e.g.,
-/

example : Nat → Nat :=
  by
    intro x
    exact x

/-
  ### Universal Quantifier in CONTEXT

  Having a proof-term of a proposition that starts with `∀ a : α ...` is equivalent
  to having a function from terms of `α` to proof-terms of `...`

  We *consume* such a hypothesis by applying it.
-/
example (h : ∀ a b : ℕ, a + b = b + a) : 2 + 3 = 3 + 2 := h 2 3

example (h : ∀ a b : ℕ, a + b = b + a) : 2 + 3 = 3 + 2 :=
  by
    apply h 2 3

/-
  EXAMPLES
-/

example : ∀ n : ℕ , (n*n).sqrt = n := Nat.sqrt_eq


#check Nat.le_refl

example : ∀ x : ℕ, x < x + 1 := fun x => Nat.lt_succ_iff.mpr (Nat.le_refl x)

example : ∀ x : ℕ, x < x + 1 := by
    intro x
    apply Nat.lt_succ_iff.mpr
    apply Nat.le_refl x

-- same as

example (x : ℕ) : x < x + 1 := by
    apply Nat.lt_succ_iff.mpr
    apply Nat.le_refl x
