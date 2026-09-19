/-
Copyright (c) 2026 Iulian Simion. All rights reserved.
Released under the 3-Clause BSD License as described in the file LICENSE.
Authors: Iulian Simion, assisted by Claude (Anthropic) and Gemini (Google)
-/
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring

/-!
# Macros

Lean processes input in two stages: the parser turns text into syntax, and the
elaborator turns syntax into terms. A **macro** rewrites syntax into other
syntax. Before the elaborator works out what a piece of syntax *means*, it
expands any macros in it, and then elaborates the result.

Much of Lean's own notation is defined by macros. A macro adds no new
semantics; it is an abbreviation.
-/

namespace MacroExamples

/-!
## A macro for a term

The declaration `macro "ℝ²" : term => `(ℝ × ℝ)` says: wherever the token
`ℝ²` appears in a position where a term is expected, replace it by `ℝ × ℝ`.

The backtick-parenthesis `` `( … ) `` is *quotation*: it produces the
expression written inside as syntax, without evaluating it. A macro whose
right-hand side is `` `(2 + 2) `` produces the expression `2 + 2`, not the
number `4`; the elaborator gives it a meaning only after the expansion.
-/

macro "ℝ²" : term => `(ℝ × ℝ)

def pair : ℝ² := (1, 2)
#check pair

/-!
## `syntax` and `macro_rules`

The `macro` keyword is a shorthand for two declarations, which can also be
written separately:

* the command `syntax` declares the grammar — what the parser should accept;
* the command `macro_rules` gives the translation, and may give several rules,
  chosen by pattern matching on the syntax.
-/

-- 1. the grammar
syntax "double_it " term : term

-- 2. the translation rules, tried in order
macro_rules
  -- if the argument is a string literal, concatenate it with itself
  | `(term| double_it $s:str) => `(term| $s ++ $s)
  -- otherwise, add it to itself
  | `(term| double_it $x:term) => `(term| $x + $x)

#eval double_it 5       -- expands to `5 + 5`
#eval double_it "Lean"  -- expands to `"Lean" ++ "Lean"`

/-!
## A macro for a tactic

The same mechanism gives a name to a tactic script. The script below is the
one from the section on `solve` in `07_Tactic_Combinators.lean`: it splits a
conjunction into its parts and closes every part that repeated `Even.add_two`
and `Even.zero` steps can prove, leaving the others unchanged.
-/

inductive Even : ℕ → Prop where
  | zero : Even 0
  | add_two : ∀ k : ℕ, Even k → Even (k + 2)

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
    repeat' sorry   -- the goals `Even 7` and `Even 3` are false

/-!
The macro `intro_and_even` is a fixed script under a new name. The *script*
inspects the goal when it runs, through `apply` and `first`, but the **macro**
does not: it only rewrites syntax and has no access to the goal, so it cannot
choose its expansion based on the goal. A tactic that inspects the goal is
written by metaprogramming (`appendix/01_Writing_Tactics.lean`).

## Macros for operators

Operators are macros too: `infixl` and `notation` expand into the `syntax`
plus `macro_rules` pair described above. The name `infixl` reads
*infix, left*: the operator is written between its two arguments, and repeated
uses group from the left, so `a ⊞ b ⊞ c` means `(a ⊞ b) ⊞ c`; `infixr` groups
from the right. The number after the colon is the operator's precedence, which
decides how tightly it binds relative to other operators.
-/

def average (x y : ℚ) : ℚ := (x + y) / 2

infixl:65 " ⊞ " => average

example (a b : ℚ) : a ⊞ b = b ⊞ a :=
  by
    unfold average
    ring

/-!
The command `notation` is the general form, for syntax that is not a symbol
between two arguments. You write the shape you want, with the arguments
interleaved.

A new notation that reuses a symbol Mathlib already defines compiles, but a
later use of that symbol is then an error whenever more than one of its
meanings fits.
-/

def sumSq (x y : ℝ) : ℝ := x ^ 2 + y ^ 2

notation "sq[" x ", " y "]" => sumSq x y

example (a b : ℝ) : sq[a, b] = sq[b, a] :=
  by
    unfold sumSq
    ring

/-!
## Exercises

Solutions: `solutions/07_Combinators_and_Macros.lean`. Further exercises:
section 7 of `09_Exercises.lean`.

### 1 — a tactic macro
Exercise 1 of `07_Tactic_Combinators.lean` proves `Even 6` with one combinator
expression. Give that expression the name `even_search`, then use it to prove
`Even 10` in one word. -/

-- macro "even_search" : tactic => sorry

theorem ex1 : Even 10 := sorry

end MacroExamples
