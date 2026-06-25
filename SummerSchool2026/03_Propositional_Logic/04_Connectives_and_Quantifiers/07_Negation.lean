/-
Copyright (c) 2026 Iulian Simion. All rights reserved.
Released under the 3-Clause BSD License as described in the file LICENSE.txt.
Authors: Iulian Simion
-/
import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Tactic.Linarith

/-
  # More on `False`

  The type `Prop` consists semantically of two terms `True` and `False`.
  Both are themselves types:
  `True` is a type consisting of one element, the witness / proof-term.
  `False` is a type consisting of no elements.

  The context is built out of assumptions / hypotheses.
  Assuming you have a proof-term for `False` (which you cannot), you can prove anything.
  This is the Principle of Explosion (Ex Falso Quodlibet).

  In proofs, we may use `False.elim` to close the GOAL.

  Programmatically, since `False` has no constructor,
  the variable `h : False` can never exist at runtime,
  so Lean does not complain since it is dead code at runtime.
-/

example (h : False) : 1 = 0 :=
  False.elim h

example (h : False) : 1 = 0 :=
  by
    exfalso
    exact h

/-
  # NOT Connective (Negation)

  Given a proposition `p`,
  the connective NOT, `¬`, constructs the proposition `¬ p`,
  which is modeled as `p → False`.

  But `False` is the empty proposition.
  So, what does it mean to have a map to an empty type?
  It means that `p` also has to be the empty type, i.e., `False`.

  As a type, `¬` is modeled with a `def` depending on propositions.
  While `False` cannot be instantiated, `p → False` can be instantiated — but only if `p` is `False`.
-/

section

#print Not
#check Not

variable (p : Prop)

#check Not p    -- this is the proposition ¬p

#check Ne

#check False.elim -- from `False` any proposition follows

end

/-
  ## NOT Connective in CONTEXT

  When we have a negation in the context
  ` ... h : ¬ p ... ⊢ t`
  we have the uncallable function `p → False`.

  To *consume* a negation, we may construct `hp : p`, which,
  applied to `p → False`, tells Lean that the context is inconsistent
  and, thus, that the target `t` has to be the proposition `False`.

  Notice that if you produce `False` in the context,
  you may use `False.elim` to close the GOAL.
-/

example (p : Prop) (hp : p) (hnp : ¬p) : False :=
    hnp hp

example (p : Prop) (hp : p) (hnp : ¬p) : p ↔ p :=
    False.elim (hnp hp)

example (p : Prop) (hp : p) (hnp : ¬p) : p ↔ ¬ p :=
    False.elim (hnp hp)

example : 1 = 0 → False :=
  fun (h : 1 = 0) => Nat.noConfusion h

example (p : Prop) (hp : p) (hnp : ¬p) : False :=
  by
    contradiction

/-
  The `contradiction` tactic tries to deduce the inconsistency of the context.

  Alternatively, one can arrange the proof by
  singling out a proof term that is present in the context
  with the `absurd` tactic.
-/

example (p : Prop) (hp : p) (hnp : ¬p) : p ↔ p :=
  by
    absurd hp
    exact hnp


example (n : ℕ) (h : ¬ n > 2) : n ≤ 2 :=
  by
    push Not at h
    exact h

/-
  ## NOT Connective in TARGET

  When we have to prove a negation
  ` ... ⊢ ¬ p ` which is the same as ` ... ⊢ p → False `,
  we *construct* a function.

  Such a function can only exist if `p` is an empty `Prop`, i.e., if `p` is `False`.

  When Lean validates the function `p → False`, it ensures that
  adding `p` to the context makes the context logically inconsistent.
-/

example (n : Nat) (h1 : n = 1) : ¬ 2 = n :=
    fun h2 : 2 = n => nomatch (Eq.trans h2 h1)


example (p : Prop) : ¬ p :=
  by
    -- apply Not.intro
    intro hp
    sorry

example (n : Nat) : n ≥ 3 → ¬ (n < 1) :=
  by
    intro hn3 hn0
    linarith -- `contradiction` does not work


/-
  EXAMPLE 1 (see [Hitch])
-/
theorem Not_Not_intro (a : Prop) :
  a → ¬¬ a :=
  by
    intro ha hna
    apply hna
    exact ha

/-
  EXAMPLE 2
-/
example (n : Nat) (h : n = 2) : n ≠ 3 :=
  by
    intro h'
    rw [h'] at h
    contradiction

example (n : Nat) (h : n = 2) : n ≠ 3 :=
  by
    linarith

/-
  In mathematical logic, when dealing with negations,
  it is standard to bring the proposition into `negation normal form (NNF)`,
  i.e., to push the negation as far into the proposition as possible.

  In Lean 4, this is done with `push Not at` which is part of Mathlib (not Lean core).

  Notice that `push Not at` focuses only on `¬`.
  It is different from `NNF` where `p → q` is converted to `¬ p ∨ q`.
-/

example : ¬(∃ m n : ℤ, ∀ t : ℝ, m < t ∧ t < n) :=
  by
    push Not
    sorry

example : ¬(∀ a : ℕ, ∃ x y : ℕ, x * y ∣ a → x ∣ a ∧ y ∣ a) :=
  by
    push Not
    sorry

example : ¬(∀ m : ℤ, m ≠ 2 → ∃ n : ℤ, n ^ 2 = m) :=
  by
    push Not
    sorry

example : ¬ ∃ x : ℝ, x-1 = 0 ∧ x+1 = 0 :=
  by
    push Not
    intro x h1 h2
    linarith

/-
  EXAMPLE (Cases will be studied in the next chapter)
-/

#check lt_trichotomy
example : ¬ (∃ n : ℕ, n ^ 2 = 2) := by
  push Not
  intro n h'
  have h:= lt_trichotomy n 1
  rcases h with (hn | hn | hn)
  · have h0 : n = 0 := by linarith
    nlinarith
  · have h1 : n = 1 := by linarith
    nlinarith
  · have h1 : n ≥ 2 := by linarith
    nlinarith
