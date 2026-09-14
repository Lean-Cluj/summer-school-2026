/-
Copyright (c) 2026 Iulian Simion. All rights reserved.
Released under the 3-Clause BSD License as described in the file LICENSE.
Authors: Iulian Simion, assisted by Claude (Anthropic) and Gemini (Google)
-/
import Mathlib.Data.Real.Basic

/-!
# Propositions, starting from equality

Lean's foundation is a formal system called the **Calculus of Inductive
Constructions** (CIC), a dependent type theory. Definitional equality
`a ≡ b : A` is a judgment of CIC: it holds, in particular, when both sides
reduce to a common normal form. A judgment is a claim about CIC rather than a
statement inside it, so it cannot be negated, joined to another by "and", or
placed under a quantifier.

Ordinary mathematics does all three constantly, so CIC represents its
statements not as judgments but as types: a proposition is a *type*, and a
proof of it is a *term* of that type. Equality is such a type.

## Equality is a type

For terms `a` and `b` of the same type, the proposition that they are equal is
written `a = b`, which is notation for `Eq a b`.
-/

section
variable (a b : ℤ)

#check Eq a b   -- a = b : Prop
#check Eq 4 5   -- 4 = 5 : Prop

end

/-!
Both are terms of type `Prop`. A proposition is also a type in its own right.
The terms of `ℕ` are numbers; the terms of a proposition are its **proofs**.

Being a proposition is not the same as being true. The expression `4 = 5` is as
well formed as `a = b`, and whether either has a proof is a separate question.
-/

#check Prop
#check ℕ

/-!
## What the declaration of `Eq` says

Equality is declared with the keyword `inductive`. This is Lean's own
declaration.
-/

namespace Illustration

inductive Eq : α → α → Prop where
  | refl (a : α) : Eq a a

end Illustration

#print Eq

/-!
The declaration names two constants, and keeping them apart is the point.
The constant `Eq` is the **type former**: a function into `Prop`, so applying
it yields a type. The constant `Eq.refl` is the **constructor**: applying it
yields a term of such a type, that is, a proof.
-/

#check @Eq        -- @Eq : {α : Sort u_1} → α → α → Prop
#check @Eq.refl   -- @Eq.refl : ∀ {α : Sort u_1} (a : α), a = a

#check Eq 3 4     -- 3 = 4 : Prop         a type
#check Eq.refl 3  -- Eq.refl 3 : 3 = 3    a proof

-- #check (Eq.refl 3 : Eq 3 4)
--   ⇒ error: Type mismatch: `Eq.refl 3` has type `3 = 3`
--     but is expected to have type `3 = 4`

/-!
So `a = b` is notation for `Eq a b`, an application of the type former; no
constructor is involved, and the expression is well formed whatever `a` and `b`
are. For example, `Eq 3 4` is such a type. It has no term, because `Eq.refl` is
the only way to build one and it builds only at `a = a`.

## `rfl` proves an equality whose two sides are definitionally equal

A proof is named with `theorem`, a declaration like `def`: a name,
a type which here is a proposition, and a term of that type, which the kernel
checks before the name enters the environment.
-/

theorem two_plus_two : (2 : ℕ) + 2 = 4 := rfl

/-!
The library definition `rfl` has body `Eq.refl a`, with the type `α` and the
term `a` both implicit. Elaborating it against the stated proposition fixes
them: `α` becomes `ℕ` and `a` becomes `2 + 2`, the left-hand side. The proof is
therefore a term of type `2 + 2 = 2 + 2`, and it is accepted at the stated type
`2 + 2 = 4` because `2 + 2` and `4` are definitionally equal, that is, because
the CIC judgment `2 + 2 ≡ 4 : ℕ` holds. The two propositions are then
definitionally equal types, and a term of the one is a term of the other.

Over the real numbers, the same proof fails, with the error shown below.
-/

-- theorem two_plus_two_real : (2 : ℝ) + 2 = 4 := rfl
--   ⇒ error: the left-hand side `2 + 2` is not definitionally equal
--     to the right-hand side `4`

/-!
A real number is not a numeral that reduces, and Mathlib defines `+` on `ℝ` in
a way that reduction cannot unfold, so reduction gets nowhere. The equality
holds, and it needs a proof rather than a computation.

The tactic `rfl` closes a goal whose two sides *compute* to the same normal
form. It therefore targets the CIC judgment `a ≡ b : A`, which is narrower than
the proposition `a = b`.

## A theorem is applied like a function

Equality is an equivalence relation. Its two remaining properties are theorems
of the library: `Eq.symm` sends a proof of `x = y` to a proof of `y = x`, and
`Eq.trans` sends proofs of `x = y` and `y = z` to a proof of `x = z`.

Since a proof is a term, supplying one is ordinary function application. It may
equally be written with the proof before the dot: `h.symm` resolves to
`Eq.symm h` because `h` has type `x = y`.
-/

#check @Eq.symm
#check @Eq.trans

/-!
The `@` in front of a name makes Lean show the implicit arguments as well.
-/

theorem symm_of_eq (x y : ℝ) (h : x = y) : y = x := h.symm

theorem trans_of_eq (x y z : ℝ) (h1 : x = y) (h2 : y = z) : x = z := h1.trans h2

/-!
So far, a proof of an equation has been passed as an argument to the theorems
above, `Eq.symm` and `Eq.trans`. It can also be used to *rewrite*: `rw [h]`
with `h : x = y` replaces `x` by `y` in the target. Here, it turns `x = 3` into
`y = 3`.
-/

example (x y : ℝ) (h : x = y) (hy : y = 3) : x = 3 :=
  by
    rw [h]
    exact hy

/-!
## A goal is a context and a target

A **binder** introduces a name with a type and fixes its scope: in
`symm_of_eq`, `(x y : ℝ)` and `(h : x = y)`. The binders before the colon are
the theorem's **hypotheses**; they enter the **context** `Γ` and remain in
scope throughout the proof, which is what makes `h.symm` a proof of `y = x`.

The proposition after the colon is the **target**. The two together are the
**goal**, which Lean displays with the hypotheses on the lines above and the
target after the turnstile:

```
x y : ℝ
h : x = y
⊢ y = x
```

What the display omits is the term. The goal is the judgment `Γ ⊢ ? : y = x`,
with its context and its type given and its term still to be produced. That
term is the proof, and tactics are ways of producing it.

A connective occurs either in the target or in the context. The rules for
constructing a proof of it in the target are its **introduction** rules; the
rules for using a proof of it in the context are its **elimination** rules.

## Two propositions at the extremes

Two propositions are named after the two extreme cases.
-/

#check True   -- has a proof
#check False  -- has no proof

/-!
The term `True.intro` is a proof of `True`, and nothing whatsoever is a proof
of `False`.

A term of a proposition is called a **proof term** when it is being built and a
**hypothesis** when it is assumed in the context.
-/

#check True.intro

/-!
## `def`, `theorem`, `example`

All three declare a term.

The keyword `def` is for data such as functions, numbers and structures.
Applied to a proposition, it triggers the linter warning shown below.
-/

-- def sum_comm_def : 1 + 2 = 2 + 1 := Nat.add_comm 1 2
--   ⇒ warning: Definition `sum_comm_def` is a proposition;
--     use `theorem` instead of `def`

/-!
The keyword `theorem` is for proofs. Lean unfolds a `def` when it needs to
compute, which is what made `rfl` prove `2 + 2 = 4` above. It does not unfold a
theorem, so later declarations use a theorem only through its statement. The
proof term is still stored and can be inspected.
-/

theorem sum_comm : 1 + 2 = 2 + 1 := Nat.add_comm 1 2

#print sum_comm

/-!
The keyword `example` is for a proof that needs no name. The proof is checked
as usual; having no name, it does not enter the environment and cannot be
referred to later.
-/

example : 1 + 2 = 2 + 1 := Nat.add_comm 1 2

/-!
## `sorry`

There is no proof of `1 = 1 + 2`. Lean nevertheless accepts `sorry`, a
placeholder standing for a missing proof. It produces a term, so the file
compiles, but the declaration is marked with a warning.
-/

theorem unproved : 1 = 1 + 2 := sorry

/-!
## Exercises

Solutions: `solutions/01_Propositions.lean`. Further exercises: section 1 of
`07_Exercises.lean`.
-/

/-! ### 1
Prove `2 + 2 = 4` with `rfl`. -/

theorem ex1 : 2 + 2 = 4 := sorry

/-! ### 2
Prove `3 * 4 = 4 * 3` by naming the lemma `Nat.mul_comm` and giving it the
right arguments. Write a *term*, not a tactic proof.

Hint: run `#check @Nat.mul_comm` first. -/

theorem ex2 : 3 * 4 = 4 * 3 := sorry

/-! ### 3
Prove `x = z` from `h1 : y = x` and `h2 : y = z`, writing the proof as a term
built from `Eq.symm` and `Eq.trans` with the dot notation.

Then write out the goal as Lean displays it, and say which part of the
judgment the display leaves out. -/

theorem ex3 (x y z : ℝ) (h1 : y = x) (h2 : y = z) : x = z := sorry
