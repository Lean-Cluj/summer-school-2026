/-
Copyright (c) 2026 Iulian Simion. All rights reserved.
Released under the 3-Clause BSD License as described in the file LICENSE.txt.
Authors: Iulian Simion
-/

/-
  Reference: Hitchhike's Guid to Logical Verification pg. 86

  `True` and `False` are modeled in different ways in Lean
  This is due to the different perspectives on the meaning

  The inductive type `Bool` encapsulates the two values
  as in any programming language
-/
#check Bool
#check Bool.true
#check Bool.false


/-
  From the perspective of propositional logic,
  `True` and `False` are two propositions, they are of type `Prop`
  Moreover, as any proposition, they are themselves types

  `True` is the type of propositions which have a proof
  `False` is the type of empty propositions, i.e. propositions without proofs
-/
#check True
#check False

/-
  Lean automatically converts between the two perspectives
-/
example : Bool.false → True := by trivial

example : Bool.false → Bool.true := by trivial

example : Bool.true → True := by trivial

example : False → Bool.true := by trivial
