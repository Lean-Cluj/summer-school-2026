/-
Copyright (c) 2026 Iulian Simion. All rights reserved.
Released under the 3-Clause BSD License as described in the file LICENSE.
Authors: Iulian Simion, assisted by Claude (Anthropic) and Gemini (Google)
-/

/-!
# Insertion sort

A **sorting algorithm** rearranges a list so that its elements appear in
non-decreasing order. Its specification has two parts: for every input list `l`,
the output must be

1. **sorted**: every element is less than or equal to each element after it;
2. a **permutation** of `l`: it contains the same elements as `l`, each as many
   times as `l` does.

The function that returns `[]` produces a sorted list, so sortedness alone does
not specify sorting.

The specification has the structure of the specification of the maximum in
`MaxList.lean`: a membership and a property. The maximum of a nonempty list `l`
is a member of `l` that is an upper bound of `l`. The sorted version of `l` is a
sorted member of `l.permutations`, the list of all permutations of `l`, which
Mathlib defines. The analogy extends to an order: the maximum is the greatest
member of `l`, and the sorted version is the least member of `l.permutations`
in lexicographic order, the order of words in a dictionary. Indeed, a
permutation that is not sorted has two adjacent elements in decreasing order,
and exchanging them gives a permutation that is smaller in this order.

**Insertion sort** sorts the rest of the list first, and then inserts the first
element at its place in the sorted result. The function `insert x l` inserts
`x` into a sorted list `l` in front of the first element `y` with `x ≤ y`.

## Implementation
-/

namespace SortingAlgorithms

def insert (x : Nat) : List Nat → List Nat
  | []      => [x]
  | y :: ys =>
      if x ≤ y then x :: y :: ys
      else y :: insert x ys

def insertSort : List Nat → List Nat
  | []      => []
  | x :: xs => insert x (insertSort xs)

/-! ## Tests -/

#eval insert 5 []                 -- [5]
#eval insert 1 [2, 3, 4]          -- [1, 2, 3, 4]
#eval insert 3 [1, 2, 4, 5]       -- [1, 2, 3, 4, 5]
#eval insert 6 [1, 2, 3]          -- [1, 2, 3, 6]
#eval insert 3 [1, 3, 5]          -- [1, 3, 3, 5]
#eval insertSort [4, 3, 5, 1, 2]  -- [1, 2, 3, 4, 5]

/-!
## Specification

This section states the specification of insertion sort as theorems and
concerns only how the statements model it. The proofs are not discussed here.

### Permutations

The proposition `l₁ ~ l₂` states that `l₁` is a permutation of `l₂`. It is
notation for `List.Perm l₁ l₂`, and it becomes available after `open List`. The
symbol `~` is the tilde of the keyboard; the similar symbol `∼`, which the input
`\sim` produces, does not denote permutations. The
predicate `List.Perm` is inductive, with four constructors:

* `Perm.nil : [] ~ []`;
* `Perm.cons x : l₁ ~ l₂ → x :: l₁ ~ x :: l₂`;
* `Perm.swap x y l : y :: x :: l ~ x :: y :: l`;
* `Perm.trans : l₁ ~ l₂ → l₂ ~ l₃ → l₁ ~ l₃`.

The library also provides `Perm.refl l : l ~ l`,
`Perm.length_eq : l₁ ~ l₂ → l₁.length = l₂.length`, and
`Perm.mem_iff : l₁ ~ l₂ → (a ∈ l₁ ↔ a ∈ l₂)`.
-/

open List

#print List.Perm

/-!
The permutation part of the specification is `insertSort_perm`. It rests on
`insert_perm`, the corresponding statement for a single insertion. The theorem
`insert_length` follows from `insert_perm`, since permutations have equal
lengths.
-/

theorem insert_perm (x : Nat) (l : List Nat) : insert x l ~ x :: l := by sorry

theorem insertSort_perm (l : List Nat) : insertSort l ~ l := by sorry

theorem insert_length (x : Nat) (l : List Nat) : (insert x l).length = l.length + 1 := by sorry

/-!
### Sortedness

The predicate `List.Pairwise R l` holds when `R a b` holds for every element `a`
of `l` and every element `b` that comes after `a` in `l`. A list is sorted when
this holds for the relation `≤`. The expression `(· ≤ ·)` denotes the function
`fun a b => a ≤ b`.

The library lemma `List.pairwise_cons` describes `List.Pairwise` on a list with
first element `a`:

  `List.Pairwise R (a :: l) ↔ (∀ b ∈ l, R a b) ∧ List.Pairwise R l`.
-/

def IsSortedPairwise (l : List Nat) : Prop := List.Pairwise (· ≤ ·) l

/-!
The sortedness part of the specification is `insertSort_sorted`.
-/

theorem insertSort_sorted (l : List Nat) : IsSortedPairwise (insertSort l) := by sorry

/-!
## Mathlib

Mathlib defines the same two functions for an arbitrary relation, as
`List.orderedInsert` and `List.insertionSort`, and proves their specification
as `List.perm_insertionSort` and `List.pairwise_insertionSort`.
-/

end SortingAlgorithms
