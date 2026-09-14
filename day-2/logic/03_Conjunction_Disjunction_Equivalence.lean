/-
Copyright (c) 2026 Iulian Simion. All rights reserved.
Released under the 3-Clause BSD License as described in the file LICENSE.
Authors: Iulian Simion, assisted by Claude (Anthropic) and Gemini (Google)
-/
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Conjunction, disjunction, equivalence

Each of these three is an inductive type, and its constructors settle both
rules. Building a proof means choosing a constructor and supplying its
arguments, which is the rule for the target; using a proof means knowing it
came from one of the constructors, which is the rule for the context.

# Conjunction

A proof of `p ∧ q` consists of a proof of `p` together with a proof of `q`.
A type whose terms bundle several things at once is declared as a
**structure**: one constructor, taking one argument per field.
-/

section
#print And

variable (p q : Prop)
#check And p q     -- this is the proposition `p ∧ q`

#check @And.intro  -- the constructor
#check @And.left   -- the first field
#check @And.right  -- the second field
end

/-!
The constructor `And.intro` builds a proof; the fields `And.left` and
`And.right` are read off a proof. Every structure has a constructor and fields
in these two roles.

## `∧` in the TARGET

The tactic `constructor` applies the constructor and leaves one goal per field,
so the single goal with target `p ∧ q` becomes two goals, targeting `p` and
`q`. The `·` bullets, typed `\.`, focus on one goal at a time.
They are optional.
-/

example (p q : Prop) (hp : p) (hq : q) : p ∧ q :=
  by
    constructor
    · exact hp
    · exact hq

example (n : Nat) (h : n = 5) : n ≥ 5 ∧ n ≤ 5 :=
  by
    constructor
    · exact ge_of_eq h
    · exact le_of_eq h

/-!
Written as a term, the proof is `And.intro hp hq`. Since `And` has exactly one
constructor, it may also be written with the **anonymous constructor** `⟨…⟩`,
typed `\<` and `\>`. Lean has to be able to tell which type is meant, and here
the goal supplies it.
-/

example (p q : Prop) (hp : p) (hq : q) : p ∧ q := And.intro hp hq

example (p q : Prop) (hp : p) (hq : q) : p ∧ q := ⟨hp, hq⟩

example (n : Nat) (h : n = 2) : n > 1 ∧ n < 7 := ⟨by linarith, by linarith⟩

/-!
## `∧` in the CONTEXT

A hypothesis `h : p ∧ q` is used by projecting out its two fields, written
`h.left` and `h.right`.
-/

example (p q : Prop) (h : p ∧ q) : q :=
  h.right

/-!
The tactic `obtain` splits the hypothesis into its components in one step and
names them:

  `obtain ⟨hp, hq⟩ := h`

replaces `h : p ∧ q` in the context by `hp : p` and `hq : q`. The pattern
`⟨hp, hq⟩` is the anonymous constructor read backwards. Where in the target it
builds a pair, in the context it takes one apart.
-/

example (p q : Prop) (h : p ∧ q) : q ∧ p :=
  by
    obtain ⟨hp, hq⟩ := h
    exact ⟨hq, hp⟩

/-!
## Example: commutativity of `∧`
-/

theorem and_swap (p q : Prop) : p ∧ q → q ∧ p :=
  by
    intro h
    obtain ⟨hp, hq⟩ := h
    exact ⟨hq, hp⟩

-- the same statement as a plain function, with no tactics at all
theorem and_swap_term (p q : Prop) : p ∧ q → q ∧ p :=
  fun h => ⟨h.right, h.left⟩

/-!
# Disjunction

A proof of `p ∨ q` is a proof of `p` *or* a proof of `q`. Building one means
having a proof of one side and naming that side; using one means handling both,
since which side was taken cannot be recovered from the proof. A type offering
a choice between alternatives is declared as an **inductive type** with one
constructor per alternative.
-/

section
#print Or

variable (p q : Prop)
#check Or p q     -- this is the proposition `p ∨ q`

#check @Or.inl    -- first constructor: from a proof of `p`
#check @Or.inr    -- second constructor: from a proof of `q`
#check @Or.elim   -- elimination: case analysis
end

/-!
## `∨` in the TARGET

There are two constructors, so building a proof means committing to a side.
The tactics `left` and `right` reduce the target `p ∨ q` to `p` or to `q`,
and the corresponding terms are `Or.inl` and `Or.inr`.
-/

example (n : Nat) (h : n = 1) : n = 2 ∨ n = 1 := Or.inr h

example (x : Nat) (h : x = 2) : x ≥ 1 ∨ x ≤ 1 :=
  by
    left
    linarith

/-!
## `∨` in the CONTEXT

With `h : p ∨ q` above the `⊢` and a goal `t`, we do not know which side holds,
so both must be handled. Using a disjunction therefore splits one goal into
two:

```
goal 1:   … hp : p …  ⊢ t
goal 2:   … hq : q …  ⊢ t
```

The tactic `obtain hp | hq := h` produces exactly that state, the bar `|`
marking alternatives where `⟨…⟩` marked components.
-/

example (p q : Prop) (h : p ∨ q) : q ∨ p :=
  by
    --rcases h with hp | hq  -- a tactic that we discuss in the afternoon
    obtain hp | hq := h
    · exact Or.inr hp
    · exact Or.inl hq

example (n : Nat) (h : n = 2 ∨ n = 3) : n ≤ 7 :=
  by
    obtain h | h := h
    · linarith
    · linarith

/-!
Written as a term, the case split is made with the elimination rule `Or.elim`.
Its type asks for a proof of `p → t` and a proof of `q → t`. The two goals it
leaves are therefore *implications* rather than the state drawn above, which is
why each branch of the term below begins with its own function abstraction.
-/

example (p q : Prop) (h : p ∨ q) : q ∨ p :=
  Or.elim h (fun hp => Or.inr hp) (fun hq => Or.inl hq)

/-!
Written out like that, the two branches are visibly `Or.inr` and `Or.inl`, so
the term shortens to `h.elim Or.inr Or.inl`. This particular statement is in
the library already, as `Or.symm`.

## A disjunction with three cases

The lemma `lt_trichotomy a b` states `a < b ∨ a = b ∨ b < a`, grouped as
`a < b ∨ (a = b ∨ b < a)`, so taking it apart with three
names at once is written `obtain h₁ | h₂ | h₃ := h`.
-/

#check @lt_trichotomy

theorem le_or_succ_le (n m : ℕ) : n ≤ m ∨ m + 1 ≤ n :=
  by
    have h := lt_trichotomy n m
    -- rcases h with h₁ | h₂ | h₃  -- a tactic that we discuss in the afternoon
    obtain h₁ | h₂ | h₃ := h
    · left
      exact le_of_lt h₁
    · left
      exact le_of_eq h₂
    · right
      linarith

/-!

# Equivalence

A proof of `p ↔ q` consists of a proof of
`p → q` together with a proof of `q → p`, so `Iff` is a structure exactly like
`And`, and the only difference is that its two fields are implications. The
fields are named after the rule that uses them: `mp` for *modus ponens*, the
forward direction, and `mpr` for its reverse.
-/

section
#print Iff

variable (p q : Prop)
#check Iff p q

#check @Iff.intro
#check @Iff.mp
#check @Iff.mpr
end

/-!
## `↔` in the TARGET

Since `Iff` is a structure with two fields, `constructor` splits a goal with
target `p ↔ q` into two goals, targeting `p → q` and `q → p`, and the anonymous
constructor works as it did for `∧`.
-/

example (p q : Prop) (hpq : p → q) (hqp : q → p) : p ↔ q := ⟨hpq, hqp⟩

example (n m : Nat) (h : n = m) : n = 7 ↔ m = 7 :=
  by
    constructor
    · intro _
      linarith
    · intro _
      linarith

/-!
## `↔` in the CONTEXT

The fields `h.mp` and `h.mpr` are the two directions, each an ordinary
implication, and `obtain` takes both apart at once.

Applying `h.mp : p → q` to `hp : p` gives a proof of `q`. This is function
application, that is, modus ponens.
-/

example (p q : Prop) (h : p ↔ q) (hp : p) : q := h.mp hp

example (p q : Prop) (h : p ↔ q) : q ↔ p :=
  by
    obtain ⟨hpq, hqp⟩ := h
    exact ⟨hqp, hpq⟩

/-!
*Rewriting* is a different operation and is also available here. The tactic
`rw` is not restricted to equalities: given `h : p ↔ q` it replaces occurrences
of `p` by `q` in the target, exactly as `rw [h]` with `h : x = y` replaced `x`
by `y` in `01_Propositions.lean`.
-/

example (p q : Prop) (h : p ↔ q) (hq : q) : p :=
  by
    rw [h]
    exact hq

/-!
## Example

Each direction of an equivalence is proved separately. Below, the
right-to-left direction splits on the disjunction it is given, and the
left-to-right direction is arithmetic.

The tactic `rw` attempts `rfl` after rewriting. In the last branch, `rw [h1]`
turns the goal into `1 ≤ 1`, which that attempt closes, since the tactic `rfl`
proves `a ≤ a`. In the branch above it, the goal becomes `0 ≤ 1`, which
the attempt does not close, so `norm_num` follows.
-/

example (n : ℕ) : n ≤ 1 ↔ n = 0 ∨ n = 1 :=
  by
    constructor
    · intro h
      -- the bound `n ≤ 1` leaves only two possibilities for `n`
      omega
    · intro h
      obtain h0 | h1 := h
      · rw [h0]      -- goal becomes `0 ≤ 1`; the `rfl` attempt does not close it
        norm_num
      · rw [h1]      -- goal becomes `1 ≤ 1`, which the `rfl` attempt closes

/-!
## Summary for `∧`, `∨` and `↔`

| Connective | TARGET                              | CONTEXT                                     |
| :--------- | :---------------------------------- | :------------------------------------------ |
| `p ∧ q`    | `constructor`, `⟨hp, hq⟩`           | `h.left`, `h.right`, `obtain ⟨hp, hq⟩ := h` |
| `p ∨ q`    | `left`, `right`, `Or.inl`, `Or.inr` | `obtain hp \| hq := h`, `Or.elim`           |
| `p ↔ q`    | `constructor`, `⟨hpq, hqp⟩`         | `h.mp`, `h.mpr`, `rw [h]`, `obtain`         |

A type with one constructor gives one goal per field in the target and
projections in the context. A type with several constructors gives a choice in
the target and a case split in the context.
-/

/-!
# Exercises

Solutions: `solutions/03_Conjunction_Disjunction_Equivalence.lean`. Further exercises: section 3 of
`07_Exercises.lean`.
-/

/-! ## 1 — a concrete conjunction
Split the goal, then let `linarith` do each half. -/

theorem ex1 (n : Nat) (h : n = 4) : n > 3 ∧ n < 5 := sorry

/-! ## 2 — case analysis on a disjunction
The disjunction is still in the target, so begin with `intro h`, then split it
with `obtain hp | hq := h`. -/

theorem ex2 (p q r : Prop) (hpr : p → r) (hqr : q → r) : p ∨ q → r := sorry

/-! ## 3 — use one direction of an equivalence -/

theorem ex3 (p q : Prop) (h : p ↔ q) (hq : q) : p := sorry
