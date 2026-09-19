/-
Copyright (c) 2026 Iulian Simion. All rights reserved.
Released under the 3-Clause BSD License as described in the file LICENSE.
Authors: Iulian Simion, assisted by Claude (Anthropic) and Gemini (Google)
-/
import Mathlib.Data.Nat.Basic

/-!
# Tactic combinators

Tactic combinators apply a tactic to several goals, retry after a failure, or
repeat a tactic until nothing changes. Two of them, `all_goals` and `<;>`,
already appeared in `04_Cases.lean`, closing every branch of a case split with
one tactic.

## The running example

The predicate `Even` below is inductive: `Even 0` holds, and `Even (k+2)`
holds whenever `Even k` does. So proving `Even 4` means applying `add_two`
twice and then `zero`.
-/

inductive Even : ℕ → Prop where
  | zero : Even 0
  | add_two : ∀ k : ℕ, Even k → Even (k + 2)

/-!
A complete proof using combinators:
-/

theorem provable_example : Even 4 ∧ Even 6 ∧ Even 8 :=
  by
    repeat' apply And.intro       -- three goals
    repeat' first                 -- and each is peeled down to `Even 0`
      | apply Even.add_two
      | apply Even.zero

/-!
The rest of the file uses the goal

  `Even 4 ∧ Even 7 ∧ Even 3 ∧ Even 0`

which is **not provable**, since `Even 7` and `Even 3` are false. On it, each
combinator closes some goals and leaves others open. The proofs below end in
`repeat' sorry`, which closes the remaining goals with `sorry` so that the file
compiles.

## `repeat'`

The combinator `repeat' tac` applies `tac` to all goals, then to all resulting
goals, and so on, until it can no longer be applied anywhere.
-/

theorem repeat'_example :
    Even 4 ∧ Even 7 ∧ Even 3 ∧ Even 0 :=
  by
    repeat' apply And.intro    -- splits the conjunction into four goals
    repeat' apply Even.add_two -- peels 2 off each numeral as far as it goes
    repeat' sorry              -- four goals left: `Even 0`, `Even 1`,
                               -- `Even 1`, `Even 0`

/-!
## `first`

The combinator `first | tac₁ | tac₂ | …` tries its alternatives in order and
keeps the first that succeeds.

Combined with `repeat'`, it applies `Even.add_two` while that applies, and
`Even.zero` on a goal `Even 0`.
-/

theorem repeat'_first_example :
    Even 4 ∧ Even 7 ∧ Even 3 ∧ Even 0 :=
  by
    repeat' apply And.intro
    repeat'
      first
      | apply Even.add_two
      | apply Even.zero
    repeat' sorry

/-!
## `all_goals`

The combinator `all_goals tac` applies `tac` exactly once to each goal, and
succeeds only if `tac` succeeds on *every* one of them. Here, it does not:
`Even 0` cannot be proved by `add_two`, so the whole call in the commented-out
proof below fails.
-/

/-
theorem all_goals_example :
    Even 4 ∧ Even 7 ∧ Even 3 ∧ Even 0 :=
  by
    repeat' apply And.intro
    all_goals apply Even.add_two   -- fails on the `Even 0` goal
    repeat' sorry
-/

/-!
## `try`

The combinator `try tac` runs `tac` and succeeds whether or not `tac` did.
Wrapping the failing step in `try` makes the `all_goals` above go through.
-/

theorem all_goals_try_example :
    Even 4 ∧ Even 7 ∧ Even 3 ∧ Even 0 :=
  by
    repeat' apply And.intro
    all_goals try apply Even.add_two
    repeat' sorry

/-!
## `any_goals`

The combinator `any_goals tac` also applies `tac` once to each goal, but
succeeds as long as it worked on *at least one*. This differs from
`all_goals try tac`, which always succeeds, whereas `any_goals` still fails if
`tac` fails on every goal.
-/

theorem any_goals_example :
    Even 4 ∧ Even 7 ∧ Even 3 ∧ Even 0 :=
  by
    repeat' apply And.intro
    any_goals apply Even.add_two
    repeat' sorry

/-!
## `solve`

The combinator `solve | tac₁ | tac₂ | …` is like `first`, except that an
alternative counts as successful only if it closes the goal completely; an
alternative that makes progress without closing the goal is rejected.

Below, the conjunction is split, and each goal is either closed entirely by
`add_two` and `zero` steps or left unchanged. The two unprovable goals are left
unchanged.
-/

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

/-!
## Non-termination

The combinator `repeat'` runs until its argument stops applying, so an argument
that always applies makes it run until a built-in limit on the number of
repetitions stops it.

The lemma `Not.intro` turns a goal `¬p` into `p → False`. But `¬p` *is*
`p → False` by definition, so the rule matches its own output: applying it
gives back a goal of exactly the shape it started from, and no progress is ever
made.

The commented-out proof below makes no progress: it stops only at that limit,
with the goal still open.
-/

/-
theorem repeat'_not_example :
    ¬ Even 1 :=
  by repeat' apply Not.intro
-/

/-!
## Summary

| Combinator        | Applies `tac` …                              | Succeeds if …            |
| :---------------- | :------------------------------------------- | :----------------------- |
| `tac₁ <;> tac₂`   | `tac₂` to every goal `tac₁` produced         | both do                  |
| `all_goals tac`   | once to each goal                            | it works on all          |
| `any_goals tac`   | once to each goal                            | it works on at least one |
| `repeat' tac`     | until it no longer applies                   | always                   |
| `try tac`         | once                                         | always                   |
| `first \| … \| …` | the first alternative that works             | one of them works        |
| `solve \| … \| …` | the first alternative that *closes* the goal | one of them closes it    |
-/

/-!
## Exercises

Solutions: `solutions/07_Combinators_and_Macros.lean`. Further exercises:
section 7 of `09_Exercises.lean`.
-/

/-! ### 1 — prove `Even 6` with one combinator expression
One line, and no tactic written out more than once. -/

theorem ex1 : Even 6 := sorry

/-! ### 2 — three cases, one closing tactic
Use `<;>`. -/

theorem ex2 (n : ℕ) (h : n = 1 ∨ n = 3 ∨ n = 5) : n % 2 = 1 := sorry
