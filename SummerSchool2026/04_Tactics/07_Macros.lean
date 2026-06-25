/-
Copyright (c) 2026 Iulian Simion. All rights reserved.
Released under the 3-Clause BSD License as described in the file LICENSE.txt.
Authors: Iulian Simion

Note: This file contains examples and text adapted from the "Hitchhiker's
Guide to Logical Verification" (Copyright 2018–2026 Anne Baanen et al.),
which is also used under the 3-Clause BSD License. Parts of this file
were synthesized with the assistance of Gemini 3.1 Pro.
-/
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring

/-
  # Macros

  At their core, macros in Lean 4 are syntax-to-syntax translators.
  They sit directly between the parser and the elaborator.
-/
namespace macros_examples

macro "ℝ²" : term => `(ℝ × ℝ)

def pair : ℝ² := (1,2)
#check pair

/-
  `macro` keyword is actually just a shortcut.
  Lean formally splits macros into two distinct steps:
  - defining the grammar (`syntax`) and
  - defining the translation (1macro_rules1).
-/

-- 1. Define the grammar
syntax "double_it " term : term

-- 2. Define the translation rules
macro_rules
  -- If the term is a string, append it to itself
  | `(term| double_it $s:str) => `(term| $s ++ $s)
  -- If it's anything else, add it to itself
  | `(term| double_it $x:term) => `(term| $x + $x)

#eval double_it 5       -- Expands to 5 + 5 (Evaluates to 10)
#eval double_it "Lean"  -- Expands to "Lean" ++ "Lean" (Evaluates to "LeanLean")

/-
  EXAMPLE: the following example is from
  Hitchhiker's Guide to Logical Verification
  by Anne Baanen, Alexander Bentkamp, Jasmin Blanchette, Johannes Hölzl, Jannis Limperg
  Chapter 8 Metaprogramming
-/
inductive Even : ℕ → Prop where
  | zero    : Even 0
  | add_two : ∀k : ℕ, Even k → Even (k + 2)

macro "intro_and_even" : tactic =>
  `(tactic|
      (repeat' apply And.intro
       any_goals
         solve
         | repeat'
             first
             | apply Even.add_two
             | apply Even.zero))

theorem intro_and_even_example :
  Even 4 ∧ Even 7 ∧ Even 3 ∧ Even 0 :=
  by
    intro_and_even
    repeat' sorry


/-
  # Macros specialized for defining operators

  In Lean 4, operators (like +, <, or any custom symbols you invent)
  are fundamentally just macros.

  `infixl` is designed specifically for creating standard binary operators.
-/
def average (x y : ℚ) : ℚ := (x + y) / 2

infixl:65 " ⊞ " => average

example (a b : ℚ) : a ⊞ b = b ⊞ a := by
  unfold average
  ring

/-
  `notation` is a highly flexible macro builder
  used when your desired syntax is more complex
  than a simple symbol sitting between two variables.
-/
def commutator {R : Type*} [Ring R] (x y : R) : R := x * y - y * x

notation (priority := high) "⁅" x ", " y "⁆" => commutator x y

example (a b : ℝ) : ⁅a, b⁆ = -⁅b, a⁆ := by
  unfold commutator
  ring
