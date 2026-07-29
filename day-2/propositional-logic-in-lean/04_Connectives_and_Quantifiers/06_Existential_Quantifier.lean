/-
Copyright (c) 2026 Iulian Simion. All rights reserved.
Released under the 3-Clause BSD License as described in the file LICENSE.txt.
Authors: Iulian Simion
-/
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

/-
  # Existential Quantifier

  The existential quantifier `∃` constructs propositions depending on other types,

  `∃ a : α, p(a)`

  It is modeled with the inductive type `Exists`
  which depends on a type `α` and a type `α → Prop`.

  A *proof term* for `∃ a : α, p(a)` is constructed from
  an element `a : α` and a proof term `h : p(a)`.
-/

section

#print Exists
#check Exists

variable (α : Type) (p : α → Prop)

#check Exists (fun a => p a)


#check Exists.intro  -- introduction rule
#check Exists.elim   -- elimination rule

end

/-
  ## Existential Quantifier in TARGET

  When proving `∃ a : α, p(a)`, we use the unique constructor with the two parameters:
  - a term `a : α`
  - a proof-term for `p(a)`.

  ### Forward Reasoning
-/

example (α : Type) (p : α → Prop) (y : α) (hy : p y) :
  ∃ x : α, p x := Exists.intro y hy

example (p : Nat → Prop) : ∃ x : Nat, p x := Exists.intro sorry sorry

example : ∃ n : Nat, 3 < n := Exists.intro 4 (Nat.lt_succ_self 3)

example : ∃ x : ℝ, 2 < x ∧ x < 3 := ⟨5 / 2, by norm_num⟩

/-
  ### Backward Reasoning

  `exists` (Lean 4 Core tactic)
  `use` (Mathlib tactic)
-/

example (α : Type) (p : α → Prop) (y : α) (hy : p y) :
  ∃ x : α, p x :=
  by
    exists y

example (α : Type) (p : α → Prop) (y : α) (hy : p y) :
  ∃ x : α, p x :=
  by
    use y

example : ∃ n : Nat, 3 < n :=
  by
    use 4
    linarith

example : ∃ n : Nat, 3 < n :=
  by
    exists 4

example : ∃ n m : Nat, n < m :=
  by
    use 2, 3
    linarith

example : ∃ n m : Nat, n < m :=
  by
    exists 2, 3


example : ∃ x : ℝ, 2 < x ∧ x < 3 :=
  by
    use 5 / 2
    norm_num

example : ∃ x : ℝ, 2 < x ∧ x < 3 :=
  by
    exists 5 / 2
    norm_num

/-
  ### Existential Quantifier in CONTEXT

  Having a proof-term of a proposition `∃ a : α, p(a)` is equivalent
  to having `a : α` and `ha : p(a)`.

  We *consume* such a proposition by:
  - eliminating the existential quantifier with `Exists.elim`
  - or by deconstructing via the anonymous constructor `⟨ ... ⟩`.
-/

example (h : ∃ n : ℕ, n ∣ 4) : 2 = 4 :=
  by
    apply Exists.elim h
    intro a hx
    sorry

example (h : ∃ n : ℕ, n ∣ 4) : 2 = 4 :=
  by
    have ⟨a,ha⟩ := h
    sorry

-- we may also construct such a statement with the constructor

example (p : ℕ → Prop) (n : ℕ) (hn : p n) : False :=
  by
    have h : ∃ x : ℕ, p n := ⟨n, hn⟩ --Exists.intro n hn
    sorry

/-
  # Unique Existence

  `∃! a : α, p(a)`

  It is instantiated with an element `a : α`, a proof term `h : p(a)`, and
  a proof term for `∀ x : α, p(x) → x = a`.
-/

example : ∃! x : ℕ, 2 < x ∧ x < 4 := by
  use 3
  constructor
  · norm_num
  · intro y hy
    --have ⟨h1,h2⟩ := hy
    linarith

example : ∃! x : ℕ, 2 < x ∧ x < 4 :=
  ⟨3, by norm_num, fun _ ⟨ _ , _ ⟩ => by linarith ⟩
