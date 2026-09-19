/-
Copyright (c) 2026 Iulian Simion. All rights reserved.
Released under the 3-Clause BSD License as described in the file LICENSE.
Authors: Iulian Simion, assisted by Claude (Anthropic) and Gemini (Google)
-/
import Mathlib.Order.MinMax
import Mathlib.Data.Vector.Mem

/-!
# The maximum of a vector

The type `List.Vector Nat n` consists of the lists of natural numbers of length
`n`. A term of it is a pair `⟨l, h⟩` of a list `l : List Nat` and a proof
`h : l.length = n`. The type depends on the natural number `n`; a type that
depends on a term in this way is called a **dependent type**.

Since the length is part of the type, a function on vectors can recurse on the
length `n` instead of on the list. A function whose argument has type
`List.Vector Nat (n + 1)` receives only nonempty lists.

## Implementation

A vector `v : List.Vector Nat (n + 1)` has a first element `v.head`; the
function `List.Vector.head` accepts only vectors whose length has the form
`n + 1`. The remaining elements form the vector `v.tail`. Its type is
`List.Vector Nat (n + 1 - 1)`, which Lean identifies with `List.Vector Nat n`
by reducing `n + 1 - 1` to `n`, that is, by unfolding the definition of
subtraction.

The function `maxVect` recurses on the length. For length `0` it returns the
value `0`, as `maxList` does for the empty list.
-/

namespace MaxVect

def maxVect : {n : Nat} → List.Vector Nat n → Nat
  | 0, _ => 0
  | _ + 1, v => max v.head (maxVect v.tail)

/-!
The type is written with its full name `List.Vector`. After `open List`, the
name `Vector` is ambiguous, since Lean core also defines a type `Vector`,
described in the section "Lean core and Mathlib" below.

## Tests

A term of type `List.Vector Nat n` is written as the anonymous constructor
`⟨l, rfl⟩`, where `rfl` proves that the list `l` has the length `n` required by
the type. The implicit argument `n` is determined when Lean checks this proof.
-/

#eval maxVect ⟨[], rfl⟩              -- 0
#eval maxVect ⟨[7], rfl⟩             -- 7
#eval maxVect ⟨[4, 12, 3, 8], rfl⟩   -- 12
#eval maxVect ⟨[42, 17, 5, 1], rfl⟩  -- 42
#eval maxVect ⟨[1, 5, 9, 20], rfl⟩   -- 20

/-!
## Specification

The specification is the one for lists, stated for the list `v.toList` of the
elements of `v`. The hypothesis `l ≠ []` becomes `n > 0`.

The two proofs below, of the upper bound and of membership, are by induction on
the length `n`. The library provides:

* `List.Vector.notMem_zero x v : x ∉ v.toList` for `v` of length `0`;
* `List.Vector.mem_succ_iff x v : x ∈ v.toList ↔ x = v.head ∨ x ∈ v.tail.toList`;
* `List.Vector.head_mem v : v.head ∈ v.toList`;
* `List.Vector.mem_of_mem_tail x v : x ∈ v.tail.toList → x ∈ v.toList`.

In the pattern `rfl | h'` of `rcases`, the name `rfl` applies to an equation
`x = v.head` and replaces `x` by `v.head` everywhere.
-/

theorem le_maxVect {n : Nat} {v : List.Vector Nat n} {x : Nat} (h : x ∈ v.toList) :
    x ≤ maxVect v := by
  induction n with
  | zero => exact absurd h (List.Vector.notMem_zero x v)
  | succ n ih =>
    rcases (List.Vector.mem_succ_iff x v).mp h with rfl | h'
    · exact Nat.le_max_left _ _
    · exact Nat.le_trans (ih h') (Nat.le_max_right _ _)

/-!
In the proof of membership, `cases n` first excludes the length `0`, which
contradicts `h : n > 0`. The induction then runs over vectors of length
`n + 1`, and the two cases are those of `maxList_mem`: one element, or at least
two.
-/

theorem maxVect_mem {n : Nat} (v : List.Vector Nat n) (h : n > 0) :
    maxVect v ∈ v.toList := by
  cases n with
  | zero => contradiction
  | succ n =>
    clear h
    induction n with
    | zero =>
      -- a vector with one element: `maxVect v` is `max v.head 0`
      change max v.head 0 ∈ v.toList
      rw [Nat.max_zero]
      exact List.Vector.head_mem v
    | succ n ih =>
      change max v.head (maxVect v.tail) ∈ v.toList
      rcases max_choice v.head (maxVect v.tail) with h1 | h2
      · rw [h1]
        exact List.Vector.head_mem v
      · rw [h2]
        exact List.Vector.mem_of_mem_tail _ v (ih v.tail)

/-!
In both cases the target is `maxVect v ∈ v.toList`. For a vector with one
element, the first `change` replaces it by `max v.head 0 ∈ v.toList`, so that
`rw [Nat.max_zero]` finds `max v.head 0` in it. For a vector with at least two
elements, the second `change` writes `maxVect v` as `max v.head (maxVect v.tail)`,
the expression that `rw [h1]` and `rw [h2]` can rewrite. The tactic `change` is
described in `MaxList.lean`.

## Other implementations

The value `0` for the vector of length `0` is a choice made by the
implementation, and the specification excludes that case with the hypothesis
`n > 0`. The two implementations below avoid this choice in different ways:
`maxVect?` returns no number for the vector of length `0`, and `maxVect'`
accepts only vectors of length `n + 1`.

### The function `maxVect?`

The function `maxVect?` returns a value of type `Option Nat`, as `maxList?`
does: `none` for the vector of length `0`, and `some m` otherwise.
-/

def maxVect? : {n : Nat} → List.Vector Nat n → Option Nat
  | 0, _ => none
  | _ + 1, v => some (v.tail.toList.foldr max v.head)

#eval maxVect? ⟨[], rfl⟩              -- none
#eval maxVect? ⟨[4, 12, 3, 8], rfl⟩  -- some 12

/-!
### The function `maxVect'`

The function `maxVect'` accepts only vectors of length `n + 1`, and its
recursion stops at vectors of length `1`. The type excludes the vector of
length `0`, so the definition needs no value for it, and the specification of
`maxVect'` needs no hypothesis on the length; exercises 1 and 2 prove it.
-/

def maxVect' {n : Nat} (v : List.Vector Nat (n + 1)) : Nat :=
  match n, v with
  | 0, v => v.head
  | _ + 1, v => max v.head (maxVect' v.tail)

#eval maxVect' ⟨[4, 12, 3, 8], rfl⟩  -- 12

/-!
### Lean core and Mathlib

Mathlib, which defines `List.Vector`, has no maximum function for it. The
maximum of a vector `v` is computed by the function `List.max?` of Lean core,
applied to the list `v.toList`. Lean core has a second type of vectors,
`Vector α n`, which stores the elements in an array of type `Array α` instead of
a list. For arrays, Lean core defines the same two functions as for lists:
`Array.max?`, which returns a value of type `Option`, and `Array.max`, which
takes a proof that the array is nonempty and returns an element, as `maxVect'`
does for vectors of length `n + 1`.
-/

/-!
## Exercises

Solutions: `solutions/MaxVect.lean`.
-/

/-! ### 1
Prove that `maxVect' v` is a member of `v`.

Hint: induction on `n`, with the case analysis of `maxVect_mem`. -/

theorem maxVect'_mem {n : Nat} (v : List.Vector Nat (n + 1)) : maxVect' v ∈ v.toList :=
  sorry

/-! ### 2
Prove that `maxVect' v` is an upper bound of `v`.

Hint: follow the proof of `le_maxVect`. In the case of length `1`, the vector
`v.tail` has length `0`. -/

theorem le_maxVect' {n : Nat} {v : List.Vector Nat (n + 1)} {x : Nat} (h : x ∈ v.toList) :
    x ≤ maxVect' v := sorry

/-! ### 3
Prove that `maxVect'` and `maxVect` agree on vectors of length `n + 1`.

Hint: induction on `n`. In the step, both sides have the form `max v.head _`,
and the term `congrArg f h` proves `f a = f b` from `h : a = b`. After
`rw [ih]`, the goal looks like `a = a`, but `rw` does not close it: the implicit
length of `v.tail` is `n + 1 + 1 - 1` on one side and `n + 1` on the other, and
the check that `rw` runs at the end does not compute the subtraction. The
tactics `exact` and `rfl` do. -/

theorem maxVect'_eq {n : Nat} (v : List.Vector Nat (n + 1)) : maxVect' v = maxVect v :=
  sorry

end MaxVect
