/-
Copyright (c) 2026 Iulian Simion. All rights reserved.
Released under the 3-Clause BSD License as described in the file LICENSE.txt.
Authors: Iulian Simion

Note: This file contains examples and text adapted from the "Hitchhiker's
Guide to Logical Verification" (Copyright 2018–2026 Anne Baanen et al.),
which is also used under the 3-Clause BSD License.
-/
import Mathlib.Data.Nat.Basic


inductive Even : ℕ → Prop where
  | zero    : Even 0
  | add_two : ∀k : ℕ, Even k → Even (k + 2)


/- ## Tactic Combinators

When programming our own tactics, we often need to repeat some actions on
several goals, or to recover if a tactic fails. Tactic combinators help in such
cases.

`repeat'` applies its argument repeatedly on all (sub…sub)goals until it cannot
be applied any further. -/

theorem repeat'_example :
  Even 4 ∧ Even 7 ∧ Even 3 ∧ Even 0 :=
  by
    repeat' apply And.intro
    repeat' apply Even.add_two
    repeat' sorry

/- The "first" combinator `first | ⋯ | ⋯ | ⋯` tries its first argument. If that
fails, it applies its second argument. If that fails, it applies its third
argument. And so on. -/

theorem repeat'_first_example :
  Even 4 ∧ Even 7 ∧ Even 3 ∧ Even 0 :=
  by
    repeat' apply And.intro
    repeat'
      first
      | apply Even.add_two
      | apply Even.zero
    repeat' sorry

/- `all_goals` applies its argument exactly once to each goal. It succeeds only
if the argument succeeds on **all** goals. -/

/-
theorem all_goals_example :
  Even 4 ∧ Even 7 ∧ Even 3 ∧ Even 0 :=
  by
    repeat' apply And.intro
    all_goals apply Even.add_two   -- fails
    repeat' sorry
-/

/- `try` transforms its argument into a tactic that never fails. -/

theorem all_goals_try_example :
  Even 4 ∧ Even 7 ∧ Even 3 ∧ Even 0 :=
  by
    repeat' apply And.intro
    all_goals try apply Even.add_two
    repeat sorry

/- `any_goals` applies its argument exactly once to each goal. It succeeds
if the argument succeeds on **any** goal. -/

theorem any_goals_example :
  Even 4 ∧ Even 7 ∧ Even 3 ∧ Even 0 :=
  by
    repeat' apply And.intro
    any_goals apply Even.add_two
    repeat' sorry

/- `solve | ⋯ | ⋯ | ⋯` is like `first` except that it succeeds only if one of
the arguments fully proves the current goal. -/

theorem any_goals_solve_repeat_first_example :
  Even 4 ∧ Even 7 ∧ Even 3 ∧ Even 0 :=
  by
    repeat' apply And.intro
    any_goals
      solve
      | repeat'
          first
          | apply Even.add_two
          | apply Even.zero
    repeat' sorry

/- The combinator `repeat'` can easily lead to infinite looping: -/

/-
-- loops
theorem repeat'_Not_example :
  ¬ Even 1 :=
  by repeat' apply Not.intro
-/
