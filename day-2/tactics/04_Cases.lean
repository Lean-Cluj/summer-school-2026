/-
Copyright (c) 2026 Iulian Simion. All rights reserved.
Released under the 3-Clause BSD License as described in the file LICENSE.
Authors: Iulian Simion, assisted by Claude (Anthropic) and Gemini (Google)
-/
import Mathlib.Data.Nat.Basic
import Mathlib.Tactic
import Mathlib.Data.Finset.Basic

/-!
# Case analysis

Every inductive type is built by a fixed list of constructors, so a term of
that type was made by one of them. The tactic `cases` uses this: it replaces a
term by each constructor in turn and produces one subgoal per constructor.
The type `Or` has two constructors, so `cases` on a disjunction gives two goals.

# `cases`

For `b : Bool`, `cases b` gives two goals, one with `b` replaced by `false`
and one with `b` replaced by `true`.
-/

example (b : Bool) : b = true ∨ b = false :=
  by
    cases b
    case false =>
      right
      rfl
    case true =>
      left
      rfl

/-!
The `case` labels are optional; bullets work too, in the order the
constructors were declared.
-/

example (b : Bool) : b = true ∨ b = false :=
  by
    cases b
    · right; rfl
    · left; rfl

/-!
A third form is `cases … with`, written like a `match` expression: each branch
is named after a constructor, and the proof fails to compile if the type gains
a constructor that no branch covers.
-/

example (b : Bool) : b = true ∨ b = false :=
  by
    cases b with
    | true => left; rfl
    | false => right; rfl

/-!
The type `Nat` has two constructors, `zero` and `succ`, so `cases n` splits
into `n = 0` and `n = k + 1`.
-/

example (n : Nat) : n + 2 > 1 :=
  by
    cases n
    · norm_num
    · norm_num

example (n : Nat) : n = 0 ∨ ∃ k, n = k + 1 :=
  by
    cases n with
    | zero => left; rfl
    | succ k => right; use k

/-!
## Nested disjunctions

The disjunction `n = 1 ∨ n = 2 ∨ n = 3` is `n = 1 ∨ (n = 2 ∨ n = 3)`, so one
`cases` produces two goals, the second of which needs splitting again.
-/

example (n : ℕ) (h : n = 1 ∨ n = 2 ∨ n = 3) : n ≤ 3 :=
  by
    cases h
    case inl h1 =>          -- n = 1
      rw [h1]; norm_num
    case inr h23 =>
      cases h23
      case inl h2 =>        -- n = 2
        rw [h2]; norm_num
      case inr h3 =>        -- n = 3
        rw [h3]             -- goal becomes `3 ≤ 3`, closed by `rw`'s `rfl` attempt

/-!
# `rcases` and `obtain`

The tactic `rcases` performs `cases` recursively, following a pattern. The
pattern `h1 | h2 | h3` names three alternatives, and `rcases` takes the nesting
apart.
-/

example (n : ℕ) (h : n = 1 ∨ n = 2 ∨ n = 3) : n ≤ 3 :=
  by
    rcases h with h1 | h2 | h3
    · rw [h1]; norm_num
    · rw [h2]; norm_num
    · rw [h3]

/-!
The tactic `obtain` does the same with the arguments the other way round. The
patterns apply **recursively**: `⟨…, …⟩` for a structure and `|` for
alternatives can be nested inside one another, so a single pattern can take
apart a hypothesis of mixed shape such as `(p ∧ q) ∨ r` in one step.
-/

example (n : ℕ) (h : n = 1 ∨ n = 2 ∨ n = 3) : n ≤ 3 :=
  by
    obtain h1 | h2 | h3 := h
    · omega
    · omega
    · omega

/-!
## One tactic for every branch

When every branch is closed by the same tactic, it can be written once.

* the combinator `all_goals tac` runs `tac` on every remaining goal and fails
  unless it succeeds on all of them;
* the combinator `tac1 <;> tac2` runs `tac1`, then runs `tac2` on every goal it
  produced.

The combinator `<;>` acts only on the goals that `rcases` produced; `all_goals`
acts on every open goal. We return to these and other tactic combinators in
`07_Tactic_Combinators.lean`.
-/

example (n : ℕ) (h : n = 1 ∨ n = 2 ∨ n = 3) : n ≤ 3 :=
  by
    rcases h with h | h | h
    all_goals omega

example (n : ℕ) (h : n = 1 ∨ n = 2 ∨ n = 3) : n ≤ 3 :=
  by rcases h <;> omega

/-!
# `fin_cases`

The tactic `cases` gives one goal per constructor. When the constructors take
no arguments, as for `Bool`, they are exactly the values. For `Fin 5` they are
not: its one constructor, `Fin.mk`, pairs a natural number with a proof that it
is less than `5`, so `cases` gives a single goal. To try every *value* a
variable can take, there is `fin_cases`: a variable of type `Fin 5` has five,
and `n` with `n ∈ {1, 2, 3}` has three.

It produces one goal per value, with the variable replaced by that value.

The type `Finset α` contains the *finite sets* of `α`s, written with braces, and
`n ∈ s` is membership.
-/

#check ({0, 2, 5} : Finset Nat)   -- a finite set of naturals

def s : Finset Nat := {1, 2, 3}

-- one goal per member of `s`
example (n : ℕ) (h : n ∈ s) : n = 1 ∨ n = 2 ∨ n = 3 :=
  by
    fin_cases h
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr rfl)

-- one goal per element of `Fin 5`
example (n : Fin 5) : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 :=
  by
    fin_cases n
    all_goals simp

-- three goals, each a concrete numerical statement
example (n : Fin 3) : n.val ^ 2 < 5 :=
  by fin_cases n <;> norm_num

-- membership in a list works the same way
example (x : ℕ) (h : x ∈ [1, 2, 3]) : x < 4 :=
  by fin_cases h <;> omega

/-!
## `interval_cases`

The tactic `interval_cases n` splits on the values of a *bounded* variable
`n : ℕ` or `n : ℤ`: it uses bounds on `n` from the context and produces one
goal per value in the range. On `ℕ` an upper bound suffices, since `0` is a
lower bound.
-/

example (n : ℕ) (h1 : 2 ≤ n) (h2 : n ≤ 5) : n ^ 2 ≤ 25 :=
  by interval_cases n <;> norm_num

/-!
In summary:

* the tactic `cases` splits a term of an inductive type by constructor;
* the tactic `fin_cases` splits a variable of a finite type, or one known to lie
  in a given finite set or list, by value;
* the tactic `interval_cases` splits a bounded variable of type `ℕ` or `ℤ` by
  value.
-/

/-!
# Exercises

Solutions: `solutions/04_Cases.lean`. Further exercises: section 4 of
`09_Exercises.lean`.
-/

/-! ## 1 — `cases` on a `Bool`
The expression `!b` is the boolean negation of `b`. -/

theorem ex1 (b : Bool) : (!b) = true ∨ (!b) = false := sorry

/-! ## 2 — `cases` on a `Nat` -/

theorem ex2 (n : ℕ) : n = 0 ∨ ∃ k, n = k + 1 := sorry

/-! ## 3 — `fin_cases` -/

theorem ex3 (n : Fin 4) : n.val * n.val ≤ 9 := sorry
