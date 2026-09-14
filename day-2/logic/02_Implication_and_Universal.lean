/-
Copyright (c) 2026 Iulian Simion. All rights reserved.
Released under the 3-Clause BSD License as described in the file LICENSE.
Authors: Iulian Simion, assisted by Claude (Anthropic) and Gemini (Google)
-/
import Mathlib.Tactic.Linarith

/-!
# Implication and the universal quantifier

From here on, new propositions are built with the logical connectives and the
quantifiers. Each comes with introduction rules, for proving it in the target,
and elimination rules, for using it in the context.

Both `→` and `∀` are function types.

## `→` is the type of functions between proofs

Given propositions `p` and `q`, the connective `→` builds the proposition
`p → q`. Its proofs are exactly the functions taking a proof of `p` to a proof
of `q`: `p → q` is the type of such functions, and `→` is the same arrow as in
function types such as `ℕ → ℕ`.
-/

section

-- The command `variable` declares something the whole `section` may use, so
-- the examples need not repeat it. The section ends at `end`.
variable (p q : Prop)

#check (p → q)

variable (hp : p) (i : p → q)

-- applying the function `i` to the proof `hp` gives a proof of `q`,
-- which is modus ponens
#check (i hp)

end

/-!
## `→` in the TARGET

The target is `p → q`, and a function has to be constructed.

Written as a term, `fun hp => …` introduces the assumption `hp : p` and the
body must be a proof of `q`.
-/

example (p q : Prop) (hq : q) : p → q :=
  fun (_ : p) => hq

/-!
In tactic mode, which the keyword `by` starts, the same step is `intro`.
Producing a function from proofs of `p` to proofs of `q` is the same as assuming
`p` and proving `q`, so `intro hp` moves `p` from the target into the context
under the name `hp`, leaving the target `q`. In the next proof, after
`intro hp`, the target is `q` and `hp : p` is in the context.
-/

example (p q : Prop) (hq : q) : p → q :=
  by
    intro hp
    exact hq

/-!
The tactic `exact e` closes the goal with the term `e`.

The two forms are interchangeable: every tactic proof elaborates to a term.
Most proofs beyond the simplest are written in tactic mode, and the files that
follow use both.

Writing `_` instead of a name introduces the assumption without naming it.
Lean then displays it as
`a✝` and marks it inaccessible. Several assumptions may be introduced at once.
-/

example (p q : Prop) : p → q → p :=
  by
    intro hp _
    exact hp

/-!
## `→` in the CONTEXT

A hypothesis `hpq : p → q` above the `⊢` is used by applying it, as any
function is applied.
-/

example (p q : Prop) (hp : p) (hpq : p → q) : q :=
  hpq hp

/-!
The same proof can be built forward from the context or backward from the
target. The tactic `have` works forward: it names an intermediate result, and
is the tactic-mode counterpart of building a term and giving it a name.
-/

example (p q : Prop) (hp : p) (hpq : p → q) : q :=
  by
    have hq : q := hpq hp
    exact hq

/-!
The tactic `apply` works backward. It changes the target from `q` to `p`,
because supplying a proof of `p` to `hpq` would produce what is wanted. On
paper, this is the step written "since `p → q`, to prove `q` it suffices to
prove `p`".

More generally, `apply e` unifies the conclusion of `e` with the goal and
leaves as new goals the arguments that remain undetermined.
-/

example (p q : Prop) (hp : p) (hpq : p → q) : q :=
  by
    apply hpq
    exact hp

/-!
Working backward with both the context and the target.
-/

theorem modus_ponens (p q : Prop) : (p → q) → p → q :=
  by
    intro hpq hp
    apply hpq
    exact hp

/-!
Forward, the proof is `fun hpq hp => hpq hp`.

## Concrete statements

When `→` links statements about numbers, the proofs keep the same shape; only
the steps in between use facts about `ℕ`.

The first example chains two hypotheses through `Eq.trans`, and so is a
function of two arguments.
-/

example (n m k : Nat) : n = m → m = k → n = k :=
  fun (h₁ : n = m) => fun (h₂ : m = k) => Eq.trans h₁ h₂

/-!
A term proof names every lemma it uses. In tactic mode, the goal is displayed
after each step, and a tactic such as `linarith` can prove an arithmetic step.
Two proofs of one statement:
-/

-- written out, naming the lemmas that justify each step
example (n : Nat) : 2 < n → 1 < n :=
  fun (h : 2 < n) => Nat.lt_of_le_of_lt (Nat.le_succ 1) h
-- here `Nat.le_succ 1 : 1 ≤ Nat.succ 1`, and `Nat.succ 1` is definitionally
-- equal to `2`, the numeral in `h`

-- in tactic mode, letting `linarith` do the arithmetic
example (n : Nat) : 2 < n → 1 < n :=
  by
    intro h
    linarith

/-!
The two forms mix inside a single proof: below, `h₂` is applied to a proof of
`n > 7` produced by the tactic block `by linarith`.
-/

example (n m : Nat) (h₁ : n = 11) (h₂ : n > 7 → m > 2) : m > 2 :=
  h₂ (by linarith)

-- the same proof with the intermediate step named
example (n m : Nat) (h₁ : n = 11) (h₂ : n > 7 → m > 2) : m > 2 :=
  by
    have h₃ : n > 7 := by linarith
    exact h₂ h₃

/-!
The expression `n > 7` is an abbreviation for `7 < n`, since `>` is a
definition that unfolds to `<`. Lean displays whichever form you wrote, so both
may appear in one goal.

## Summary for `→`

| Connective | TARGET                    | CONTEXT           |
| :--------- | :------------------------ | :---------------- |
| `p → q`    | `intro hp`, `fun hp => …` | `apply h`, `h hp` |

## `∀` is the same function type, made dependent

Given a type `α` and a family of propositions `p : α → Prop`, the quantifier
`∀` builds the proposition `∀ a : α, p a`. Its proofs are the functions taking
a term `a : α` to a proof of `p a`.

In Lean, `∀ a : α, p a` and the dependent function type `(a : α) → p a` are the
same thing, and `→` is the special case where the result does not mention `a`.
-/

section
variable (p : Nat → Prop)

#check (∀ n : Nat, p n)
#check ((n : Nat) → p n)

-- the two are the same term, and the two `#check`s above print identically
example : (∀ n : Nat, p n) = ((n : Nat) → p n) := rfl

end

/-!
## `∀` in the TARGET

Since the goal is a function type, `intro` is again the tactic, and it names
the argument.
-/

example : ∀ a b : Nat, a + b = b + a :=
  fun a b => Nat.add_comm a b

example : ∀ a b : Nat, a + b = b + a :=
  by
    intro a b
    exact Nat.add_comm a b

/-!
Writing the variable to the left of the colon states the same proposition
differently, since Lean quantifies over the arguments automatically: in that
form the variable is in the context when the proof starts.

The tactic `intro` is not restricted to propositions. It introduces the
argument of any function type.
-/

example : Nat → Nat :=
  by
    intro x
    exact x

/-!
## `∀` in the CONTEXT

A hypothesis `h : ∀ a : α, p a` is a function, and it is used by applying it to
a particular `a`, which specialises the statement.
-/

example (h : ∀ a b : ℕ, a + b = b + a) : 2 + 3 = 3 + 2 :=
  h 2 3

/-!
Most lemmas in Lean core and in Mathlib are `∀` statements, and most are
written in the form just described, with the variables to the left of the
colon. The lemma `Nat.le_refl`, from Lean core, is declared `(n : ℕ) : n ≤ n`,
and the `#check` below prints its type as `∀ (n : ℕ), n ≤ n`: a function from
a natural number to a proof.
-/

#check @Nat.le_refl
#check @Nat.lt_succ_of_le

example : ∀ x : ℕ, x < x + 1 :=
  fun x => Nat.lt_succ_of_le (Nat.le_refl x)

example (x : ℕ) : x < x + 1 :=
  by
    apply Nat.lt_succ_of_le
    exact Nat.le_refl x

/-!
The tactic `apply` above is the backward step: it turns the target `x < x + 1`
into the target `x ≤ x` that `Nat.lt_succ_of_le` still needs, and `exact`
finishes with `Nat.le_refl x`, a complete proof of that target.

The same statement is also the Mathlib lemma `lt_add_one`, which holds over
`ℤ`, `ℚ` and `ℝ` as well.
-/

#check @lt_add_one

example (x : ℕ) : x < x + 1 := lt_add_one x

/-!
## Summary for `∀`

Because `∀` is a function type, both entries are the entries for `→`.

| Quantifier | TARGET                  | CONTEXT          |
| :--------- | :---------------------- | :--------------- |
| `∀ a, p a` | `intro a`, `fun a => …` | `apply h`, `h a` |
-/

/-!
## Exercises

Solutions: `solutions/02_Implication_and_Universal.lean`. Further exercises: section 2 of
`07_Exercises.lean`.
-/

/-! ### 1 — transitivity of implication
Prove it in tactic mode. -/

theorem ex1 (p q r : Prop) : (p → q) → (q → r) → (p → r) := sorry

/-! ### 2 — prove a `∀` as a term
Write a function whose body proves `n + 0 = n`. The proof does not need to
mention the argument by name, so Lean will suggest writing the binder as
`_`. -/

theorem ex2 : ∀ n : Nat, n + 0 = n := sorry

/-! ### 3 — consume a `∀`
The hypothesis is a function; apply it. -/

theorem ex3 (h : ∀ n : Nat, n ≤ n + 1) : 5 ≤ 6 := sorry
