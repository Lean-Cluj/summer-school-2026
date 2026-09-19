/-
Copyright (c) 2026 Iulian Simion. All rights reserved.
Released under the 3-Clause BSD License as described in the file LICENSE.
Authors: Iulian Simion, assisted by Claude (Anthropic) and Gemini (Google)
-/
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push

/-!
# The existential quantifier, and negation

The existential quantifier is an inductive type pairing data with a proof
about that data. Negation is defined as an implication: `¬p` is `p → False`.
Combined, they express non-existence, and the file ends with a proof that no
natural number squares to 2, the statement `¬∃ n : ℕ, n ^ 2 = 2`.

# The existential quantifier

Given a type `α` and a predicate `p : α → Prop`, the quantifier `∃` builds
the proposition `∃ a : α, p a`, notation for `Exists (fun a => p a)`. The
binder of the quantifier is the binder of that lambda.

Like `And`, the type has a single constructor, but its first argument is
**data**: a term `a : α`, called the **witness**, followed by a proof of `p a`
for that particular `a`.

The quantifiers `∀` and `∃` are built differently. The proposition
`∀ a : α, p a` *is* the function type `(a : α) → p a`, so a proof is a function
and `intro` introduces its argument. The proposition `∃ a : α, p a` is the
inductive type `Exists` applied to a function, so a proof is built by
`Exists.intro`, which takes the witness as its first argument.
-/

section
#print Exists

variable (α : Type) (p : α → Prop)

#check @Exists        -- the type former: it takes a predicate
#check @Exists.intro  -- the constructor
#check @Exists.elim   -- the elimination rule

-- the proposition `∃ a : α, p a` is `Exists` applied to a lambda
#check (Exists fun a : α => p a)
example : (∃ a : α, p a) = Exists (fun a : α => p a) := rfl
end

/-!
## `∃` in the TARGET

The tactic `use` supplies the witness and leaves the remaining statement as the
goal. It takes several witnesses at once for a nested `∃`, and then tries to
close the remaining goal with a small amount of automation, so the goal is
sometimes closed at once. Lean core has `exists`, which does much the same;
`use` is Mathlib's.
-/

example : ∃ n : Nat, 3 < n :=
  by
    use 4
    linarith

-- several witnesses at once, for a nested `∃`
example : ∃ n m : Nat, n < m :=
  by
    use 2, 3
    linarith

example : ∃ x : ℝ, 2 < x ∧ x < 3 :=
  by
    use 5 / 2
    norm_num

/-!
Written as a term, the proof is a pair, built with `Exists.intro` or with the
anonymous constructor.
-/

example : ∃ x : ℝ, 2 < x ∧ x < 3 := ⟨5 / 2, by norm_num⟩

/-!
## `∃` in the CONTEXT

A hypothesis `h : ∃ a : α, p a` is used by naming its two components: an
unspecified `a : α`, and a proof `ha : p a`. They are named with `obtain`,
using the same `⟨…⟩` pattern as for `∧`.
-/

example (h : ∃ n : ℕ, 3 < n) : ∃ n : ℕ, 2 < n :=
  by
    obtain ⟨a, ha⟩ := h
    exact ⟨a, by linarith⟩

/-!
## Unique existence

The proposition `∃! a : α, p a` says that there is exactly one `a` with `p a`.
Its proof has three components: a witness `a`, a proof of `p a`, and a proof of
`∀ y, p y → y = a`.
-/

example : ∃! x : ℕ, 2 < x ∧ x < 4 :=
  by
    use 3
    constructor
    · -- 2 < 3 ∧ 3 < 4
      norm_num
    · -- any `y` with 2 < y < 4 equals 3
      intro y hy
      omega

/-!
Written as a term, the three components go into one anonymous constructor.
The proposition `∃! a : α, p a` is `∃ a : α, p a ∧ ∀ y, p y → y = a`, so the
components are nested as `⟨3, ⟨_, _⟩⟩`; `⟨…⟩` flattens that nesting, and
`⟨3, _, _⟩` is accepted.
-/

example : ∃! x : ℕ, 2 < x ∧ x < 4 :=
  ⟨3, by norm_num, fun y hy => by omega⟩

/-!
## Summary for `∃`

| Quantifier | TARGET             | CONTEXT               |
| :--------- | :----------------- | :-------------------- |
| `∃ a, p a` | `use a`, `⟨a, ha⟩` | `obtain ⟨a, ha⟩ := h` |

# Negation

Negation is an abbreviation, defined in terms of the proposition `False`.

## `False`

The proposition `False` has no proof: as a type it has no terms and no
constructors.

Consequently, from `h : False` in the context, a proof of any proposition
follows: a case analysis on `h` has one case per constructor of `False`, and
there are none, so no goals remain. This is the **principle of explosion**, and
in Lean it is the function `False.elim : False → C` for any `C`.

It is the type-theoretic form of a familiar fact about sets: there is
exactly one function from the empty set to any set `X`, because there is no
element at which to define it.
-/

#check @False.elim

example (h : False) : 1 = 0 :=
  False.elim h

/-!
So `False.elim h` closes any goal. The tactic `exfalso` works from the other
side, replacing the current target by `False`, which is then what you have to
produce.
-/

example (h : False) : 1 = 0 :=
  by
    exfalso
    exact h

/-!
Both directions use `False.elim`. Forward, `False.elim h` takes a proof of
`False` obtained from an inconsistent context and closes any goal. Backward,
`exfalso` replaces the target by `False`, the same step as `apply False.elim`.

## Negation is an abbreviation

Given a proposition `p`, the connective `¬` builds `¬p`, and it is *defined* as
`p → False`.
-/

section
#print Not

variable (p : Prop)

#check Not p    -- this is the proposition `¬p`
#check @Ne      -- the expression `a ≠ b` is notation for `Ne a b`, which unfolds to `¬ (a = b)`
end

/-!
A proof of `¬p` is a term of `p → False`: it converts any proof of `p` into a
proof of `False`. Since no proof of `False` can exist, neither can a proof of
`p`, so such a term is a refutation of `p`.

In set-theoretic terms, a function `X → ∅` exists only when `X` is empty,
since an element of `X` would have to be sent somewhere. In the same way, a
proof of `¬p` exists only when `p` has no proof.

## `¬` in the TARGET

The target `¬p` is the target `p → False`, so it is proved like any
implication: `intro hp` assumes `p`, and the remaining target is `False`.
-/

example (p : Prop) : ¬(p ∧ ¬p) :=
  by
    intro h
    -- h : p ∧ ¬p, goal : False
    exact h.right h.left

-- the same thing as a term
example (p : Prop) : ¬(p ∧ ¬p) :=
  fun h => h.right h.left

example (n : Nat) : n ≥ 3 → ¬(n < 1) :=
  by
    intro hn3 hn0
    linarith

/-!
### Example: introducing a double negation

As a function: given `ha : a`, we must build a function from
`¬a` to `False`, and applying `hna : ¬a` to `ha` is exactly that.
-/

theorem not_not_intro' (a : Prop) : a → ¬¬a :=
  by
    intro ha hna
    exact hna ha

/-!
This direction stays within the rules of CIC; nothing further is assumed.
The converse, `¬¬a → a`, does not follow from them and needs a classical
axiom.

## `¬` in the CONTEXT

A hypothesis `hnp : ¬p` is a function `p → False`. It is used by applying it to
a proof of `p`, which gives `False`. A context containing both `p` and `¬p` is
inconsistent, and this application derives `False` from it.
-/

example (p : Prop) (hp : p) (hnp : ¬p) : False :=
  hnp hp

/-!
The tactic `contradiction` searches the context for a contradiction, such as a
pair of hypotheses `p` and `¬p`, or a hypothesis that computation shows to be
false, such as `3 = 2`, and closes the goal, whatever the goal is.
-/

example (p : Prop) (hp : p) (hnp : ¬p) : False :=
  by
    contradiction

example (n : Nat) (h : n = 2) : n ≠ 3 :=
  by
    intro h'        -- h' : n = 3
    rw [h'] at h    -- h : 3 = 2
    contradiction

/-!
## Summary for `¬`

Because `¬p` *is* `p → False`, both entries are the entries for `→`.

| Connective | TARGET                                 | CONTEXT                         |
| :--------- | :------------------------------------- | :------------------------------ |
| `¬p`       | `intro hp`, leaving the target `False` | `contradiction`, `h hp : False` |

## Pushing negations inward

The Mathlib tactic `push Not` moves negations inward, past quantifiers and
connectives.

Its rules include the following.

```
¬(∃ x, p x)   becomes   ∀ x, ¬ p x
¬(p ∧ q)      becomes   p → ¬q
¬(a < b)      becomes   b ≤ a
¬(∀ x, p x)   becomes   ∃ x, ¬ p x     ← classical
```

The first three are constructive. The fourth is not: turning "not every `x`
satisfies `p`" into "some particular `x` fails" asserts a counterexample that
no proof has produced, and it uses a classical axiom.

Applied to a hypothesis with `at`, `push Not` rewrites that hypothesis in
place.
-/

example (p : ℕ → Prop) (h : ¬∃ n, p n) : ∀ n, ¬ p n :=
  by
    push Not at h
    exact h

example : ¬∃ x : ℝ, x - 1 = 0 ∧ x + 1 = 0 :=
  by
    push Not
    -- goal : ∀ x, x - 1 = 0 → x + 1 ≠ 0
    intro x h1 h2
    linarith

/-!
## A longer example

The theorem below states that no natural number squares to 2. The proof pushes
the negation inward, assumes a witness, splits into three cases with
`lt_trichotomy`, and derives `False` in each; `omega`, `norm_num` and
`nlinarith` settle the arithmetic.
-/

#check @lt_trichotomy

example : ¬∃ n : ℕ, n ^ 2 = 2 :=
  by
    push Not
    intro n hn
    -- hn : n ^ 2 = 2, goal : False. Compare `n` with 1 and rule out each case.
    have h := lt_trichotomy n 1
    obtain hn1 | hn1 | hn1 := h
    · have h0 : n = 0 := by omega
      rw [h0] at hn
      norm_num at hn
    · rw [hn1] at hn
      norm_num at hn
    · have h2 : n ≥ 2 := by omega
      nlinarith

/-!
# Exercises

Solutions: `solutions/04_Existential_and_Negation.lean`. Further exercises: section 4 of
`07_Exercises.lean`.
-/

/-! ## 1 — supply a witness
Any witness will do, as long as you can prove the statement for it. -/

theorem ex1 : ∃ n : Nat, n > 100 := sorry

/-! ## 2 — reuse a witness you were given
Writing `obtain ⟨a, ha⟩ := h` names the witness and the proof. -/

theorem ex2 (h : ∃ n : Nat, n > 5) : ∃ n : Nat, n > 3 := sorry

/-! ## 3 — no natural number has successor zero
Start with `push Not` and see what the goal becomes. -/

theorem ex3 : ¬∃ n : Nat, n + 1 = 0 := sorry
