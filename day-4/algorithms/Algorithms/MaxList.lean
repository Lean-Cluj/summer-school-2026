/-
Copyright (c) 2026 Iulian Simion. All rights reserved.
Released under the 3-Clause BSD License as described in the file LICENSE.
Authors: Iulian Simion, assisted by Claude (Anthropic) and Gemini (Google)
-/
import Mathlib.Order.MinMax

/-!
# The maximum of a list

In Lean, an algorithm is written as a function.

The first algorithm of this session computes the largest element of a list of
natural numbers.
It compares the first element with the largest element of the rest of the list
and returns the larger of the two.

## Lists

The type `List Nat` of finite sequences of natural numbers is an inductive type,
like `Nat`. Its two constructors are `[]`, the empty list, and `x :: xs`, the
list with first element `x` followed by the list `xs`.
-/

#print Nat
#print List

#check ([] : List Nat)      -- [] : List ℕ
#eval 4 :: [12, 3]          -- [4, 12, 3]
#eval 4 :: 12 :: 3 :: []    -- [4, 12, 3]

example : [4, 12, 3] = 4 :: 12 :: 3 :: [] := rfl

/-!
## Implementation

The definition has one equation for each of the two constructors, `[]` and
`x :: xs`. The left side of an equation is a **pattern**, and the variables `x`
and `xs` of the pattern `x :: xs` name the parts of the input. A recursion is
**structural** when the argument of each recursive call occurs in the pattern
below a constructor, as `xs` in `x :: xs`, or as `n` in the pattern `n + 1` of a
function on `ℕ`. Each recursive call is then on a smaller input, so the
evaluation terminates, and Lean accepts the definition without a proof of
termination.
-/

namespace MaxList

def maxList : List Nat → Nat
  | [] => 0
  | x :: xs => max x (maxList xs)

/-!
The recursion needs a value at `[]`, since every computation of `maxList` ends
there. This value is compared with every element of the list, so it must not
change the result. The value `0` has this property: it is the least natural
number, so `max x 0 = x` for every `x`.
-/

/-!
## Tests

The command `#eval` compiles an expression to executable code, runs the code,
and shows the resulting value in the Infoview.
-/

#eval maxList []              -- 0
#eval maxList [7]             -- 7
#eval maxList [4, 12, 3, 8]   -- 12
#eval maxList [42, 17, 5, 1]  -- 42
#eval maxList [1, 5, 9, 20]   -- 20

/-!
## Specification

For a nonempty list `l`, the largest element `m` has two properties:

1. `m` is an **upper bound** of `l`: every `x ∈ l` satisfies `x ≤ m`;
2. `m` is a **member** of `l`: `m ∈ l`.

The two properties determine `m`; exercise 1 asks for a proof of this.

The first property also holds for the empty list, which has no elements. The
second fails for it, since `0 ∉ []`, so its statement assumes `l ≠ []`.

## Membership as an inductive predicate

The proposition `x ∈ l` is notation for `Membership.mem l x`, which for lists
is defined as `List.Mem x l`. The predicate `List.Mem` is declared with the
keyword `inductive`, and its two constructors are the two ways to prove
membership:

* `List.Mem.head as : a ∈ a :: as`, so the first element is a member;
* `List.Mem.tail b h : a ∈ b :: as`, built from `h : a ∈ as`, so a member of
  the rest is a member.
-/

#print List.Mem

/-!
Both constructors, `head` and `tail`, prove membership in a list of the form
`b :: as`, so neither proves `a ∈ []`. The tactic `cases h` replaces the goal by
one goal for each constructor that could have built `h`. For `h : x ∈ []` there
is no such constructor, so `cases h` proves the goal. For `h : x ∈ y :: ys`, it
produces two goals: in the goal from the constructor `head`, `y` is replaced by
`x`; the goal from the constructor `tail` has a new hypothesis `x ∈ ys`.

## The maximum is an upper bound

The proof is by **structural induction** on `l`: it has one case for each
constructor of `List`, `nil` and `cons`, and in the case `cons y ys` the
induction hypothesis `ih` states the property for `ys`. In that case, `cases h`
distinguishes how `x` is a member of `y :: ys`.
-/

theorem le_maxList {l : List Nat} {x : Nat} (h : x ∈ l) : x ≤ maxList l := by
  induction l with
  | nil => cases h
  | cons y ys ih =>
    cases h with
    | head _ =>
      -- here `y` has been replaced by `x`
      unfold maxList
      exact Nat.le_max_left _ _
    | tail _ h' =>
      -- here `h' : x ∈ ys`, so `x ≤ maxList ys ≤ max y (maxList ys)`
      unfold maxList
      exact Nat.le_trans (ih h') (Nat.le_max_right _ _)

/-!
The tactic `unfold maxList` replaces `maxList (y :: ys)` by the right side of its
defining equation, `max y (maxList ys)`. It makes this form visible in the
Infoview; the proof also works without it, since `exact` unfolds the definition
itself. The library lemmas
`Nat.le_max_left a b : a ≤ max a b` and `Nat.le_max_right a b : b ≤ max a b`
compare a number with the maximum of two numbers.
-/

/-!
## The maximum is a member

The proof is again by structural induction on `l`. In the case `cons x xs`, the
tactic `cases xs` distinguishes two cases.

* If `xs` is `[]`, then `maxList [x]` is `max x 0`, which is `x` by the lemma
  `Nat.max_zero`.
* If `xs` is `y :: ys`, the lemma `max_choice a b : max a b = a ∨ max a b = b`
  states that the maximum of two numbers is one of them. In the first case, the
  result is the first element `x`. In the second, it is `maxList (y :: ys)`,
  which is a member of `y :: ys` by the induction hypothesis.
-/

theorem maxList_mem {l : List Nat} (h : l ≠ []) : maxList l ∈ l := by
  induction l with
  | nil => contradiction
  | cons x xs ih =>
    cases xs with
    | nil =>
      change max x 0 ∈ [x]
      rw [Nat.max_zero]
      exact List.Mem.head _
    | cons y ys =>
      change max x (maxList (y :: ys)) ∈ x :: y :: ys
      rcases max_choice x (maxList (y :: ys)) with hx | hm
      · -- the maximum is the first element
        rw [hx]
        exact List.Mem.head _
      · -- the maximum is the maximum of the rest
        rw [hm]
        exact List.Mem.tail _ (ih (List.cons_ne_nil y ys))

/-!
The tactic `change t` replaces the target by `t`, provided that the two are
definitionally equal: Lean turns one into the other by unfolding definitions
and computing. In the proof, `change max x 0 ∈ [x]` replaces the target
`maxList [x] ∈ [x]`, so that `rw [Nat.max_zero]` finds `max x 0` in it.
The second `change` writes `maxList (x :: y :: ys)` as
`max x (maxList (y :: ys))`, the expression that `rw [hx]` and `rw [hm]` can
rewrite.

## Axioms

The command `#print axioms` lists the axioms on which a proof depends. Both
proofs above depend only on `propext`, the axiom that two equivalent
propositions are equal. Neither depends on `Classical.choice`, the axiom from
which Lean derives the law of excluded middle, so neither proof uses classical
logic.
-/

#print axioms le_maxList   -- 'MaxList.le_maxList' depends on axioms: [propext]
#print axioms maxList_mem  -- 'MaxList.maxList_mem' depends on axioms: [propext]

/-!
The lemma `max_choice` uses the definition `max a b = if a ≤ b then b else a`.
An `if` on a proposition `p` needs a decision between `p` and `¬ p`. For an
arbitrary proposition, this decision is available only through the axiom
`Classical.choice`. However, for natural numbers, `a ≤ b` is decidable: Lean
computes the decision, and the `if` needs no axiom.
-/

/-!
## Other implementations

The value `0` for the empty list is a choice made by the implementation, and the
specification excludes that case with the hypothesis `l ≠ []`. The two
implementations below avoid this choice in different ways: `maxList?` returns
no number for the empty list, and the recursion of `maxList'` stops at a list
with one element instead of at `[]`.

### The function `maxList?`

The type `Option Nat` is an inductive type, like `List Nat`. Its two
constructors are `none`, which stands for the absence of a value, and `some n`,
which holds a natural number `n`. The library function `List.head?` returns the
first element of a list in this form.
-/

#print Option

#check (none : Option Nat)   -- none : Option ℕ
#check some 4                -- some 4 : Option ℕ
#eval [4, 12, 3].head?       -- some 4
#eval ([] : List Nat).head?  -- none

/-!
The function `maxList?` returns `none` for the empty list. It uses `List.foldr`,
which combines the elements of a list from the right:
`List.foldr f a [x₁, x₂, x₃]` is `f x₁ (f x₂ (f x₃ a))`. Hence `xs.foldr max x`
is the largest of `x` and the elements of `xs`.
-/

def maxList? : List Nat → Option Nat
  | [] => none
  | x :: xs => some (xs.foldr max x)

#eval maxList? []             -- none
#eval maxList? [4, 12, 3, 8]  -- some 12

/-!
### The function `maxList'`

The function `maxList'` has a separate equation for a list with one element, and
its recursion stops there. For a nonempty list, the value `0` at `[]` is
therefore never used.
-/

def maxList' : List Nat → Nat
  | [] => 0
  | [x] => x
  | x :: y :: ys => max x (maxList' (y :: ys))

#eval maxList' [4, 12, 3, 8]  -- 12

/-!
### Lean core and Mathlib

Both libraries define this function, for lists with elements of other types as
well. The Lean core library defines `List.max?`, which returns a value of type
`Option`, as `maxList?` does, and `List.max`, which takes a proof that the list
is nonempty and therefore needs no value for the empty list. Mathlib defines `List.maximum`, which returns a
value of type `WithBot α`: the type `α` together with an added least element
`⊥`, read "bottom", from which the type takes its name. The result for the empty
list is `⊥`.
-/

/-!
## Exercises

Solutions: `solutions/MaxList.lean`.
-/

/-! ### 1
Prove that the two properties of the specification determine the maximum: a
member `m` of `l` that is an upper bound of `l` is equal to `maxList l`.

Hint: `Nat.le_antisymm` proves `a = b` from `a ≤ b` and `b ≤ a`, and
`List.ne_nil_of_mem hm` proves `l ≠ []` from `hm : m ∈ l`. -/

theorem maxList_unique {l : List Nat} {m : Nat} (hm : m ∈ l) (hub : ∀ x ∈ l, x ≤ m) :
    maxList l = m := sorry

/-! ### 2
Prove that the maximum of two lists joined by `++` is the larger of their two
maxima.

Hint: induction on `l₁`. The lemmas `Nat.zero_max a : max 0 a = a` and
`Nat.max_assoc a b c : max (max a b) c = max a (max b c)` are needed. -/

theorem maxList_append (l₁ l₂ : List Nat) :
    maxList (l₁ ++ l₂) = max (maxList l₁) (maxList l₂) := sorry

/-! ### 3
Prove that `maxList'` and `maxList` compute the same function.

Hint: follow the proof of `maxList_mem`, with induction on `l` and then `cases`
on the rest of the list. -/

theorem maxList'_eq (l : List Nat) : maxList' l = maxList l := sorry

end MaxList
