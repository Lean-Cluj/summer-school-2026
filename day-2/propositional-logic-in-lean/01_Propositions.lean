/-
Copyright (c) 2026 Iulian Simion. All rights reserved.
Released under the 3-Clause BSD License as described in the file LICENSE.txt.
Authors: Iulian Simion
-/

/-
  # Propositions

  Propositions in Lean are terms of type `Prop`.

  `Prop` itself is of type `Type` as are `Nat` or `List α`.

  For example, `2 = 1 + 1` is a proposition; we may check that the type is `Prop`:
-/

#check (2 = 1 + 1)
#check (1 = 1 + 1)

#check Prop
#check Nat
#check List Nat

/-
  Behind the scenes, the equality symbol `=` is modeled by `Eq`.

  For any type `α`,

  `Eq` is a type that takes two elements `a` and `b` of a common type `α`
  and builds the proposition that `a` and `b` are equal.

  `Eq` may be viewed as a map `Eq : α → α → Prop`.

  As a type, `Eq` is modeled with the keyword `inductive`.
-/

#check (Eq 2 (1 + 1))

/-
  Similarly, `<` is modeled by the type `LT`.

  Inequalities are modeled by the constructor `LT.lt : α → α → Prop`.

  As a type, `LT` is modeled with the keyword `class`.
-/

#check (0 < 3)

#check (LT.lt 0 3)

#check (LT.lt 3 0)

/-
  `Prop` models the universe of all propositions in Lean.

  Syntactically (form), there are infinitely many terms of type `Prop`, i.e., valid expressions that are well-formed propositions.

  Semantically (meaning), `Prop` has two elements: `True` and `False`.

  Each proposition is itself a type, and it is either inhabited (has a proof / has a witness) or not.

   - If a proposition is inhabited, it is true (it equals the element `True` of `Prop`).
   - If a proposition is not inhabited, it is false (it equals the element `False` of `Prop`).

-/

#check True  -- The proposition with a proof
#check False -- The proposition with no proof

/-
  To prove that a proposition `P` is true, you show that there is a term of type `p`.
  Then, the fact that `p` is true is formulated equivalently as:
    - `p` is inhabited
    - `p` has a witness
    - `p` has a proof
    - `p` is `True`

  For a true proposition it is possible to construct a proof-term `hp`:
  `hp : p : Prop : Type`

  For example,
  we define a term called `my_prop` of type `3 = 1 + 2` by invoking the theorem `Nat.one_add`,
  but we will not be able to define a term of type `1 = 1 + 1` since it is false.
-/

def my_prop : 3 = 1 + 2 := Nat.one_add 2
def my_prop2 : 3 = 1 + 2 := by rfl
def my_prop3 : 3 = 1 + 2 := by trivial

def my_prop4 : 1 = 1 + 2 := sorry

/-
  While `def` is used to define terms of any type, `theorem` is used to define terms of type `Prop`.

  Defining a proof term with `theorem` tells Lean to check the proposition once and then forget about the proof.

  `example` is equivalent to `theorem` but it does not give a name to the proof term.
-/

theorem my_prop5 : 3 = 1 + 2 := by rfl

example : 3 = 1 + 2 := by rfl
