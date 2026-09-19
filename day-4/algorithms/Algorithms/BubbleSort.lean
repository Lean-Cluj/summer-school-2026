/-
Copyright (c) 2026 Iulian Simion. All rights reserved.
Released under the 3-Clause BSD License as described in the file LICENSE.
Authors: Iulian Simion, assisted by Claude (Anthropic) and Gemini (Google)
-/
import Algorithms.InsertSort

/-!
# Bubble sort

**Bubble sort** repeats a **pass** over the list. A pass compares each pair of
adjacent elements, from the front of the list to its end, and exchanges the two
when the first is greater than the second. After one pass, the largest element
is at the end of the list. After `k` passes, the `k` largest elements are at the
end, in non-decreasing order, so a list of length `n` is sorted after `n - 1`
passes. The statements below use `n` passes, which keeps them simpler.

The function `bubble` performs one pass, and `bubbleSort l n` performs `n`
passes on `l`. The specification is the one of `InsertSort.lean`: the output is
sorted, and it is a permutation of the input.

## Implementation
-/

namespace SortingAlgorithms

def bubble : List Nat → List Nat
  | [] => []
  | [x] => [x]
  | x :: y :: tail =>
    if x > y then y :: bubble (x :: tail)
    else x :: bubble (y :: tail)

def bubbleSort : List Nat → Nat → List Nat
  | l, 0 => l
  | l, n + 1 => bubbleSort (bubble l) n

/-!
The recursion of `insert` and `insertSort` is structural: their recursive calls
are on the tail of the input. The recursive call `bubble (x :: tail)` is on a
list that does not occur in the pattern `x :: y :: tail`, so Lean defines
`bubble` by well-founded recursion, as `toBits`, with the size `sizeOf` of lists
as measure. For a list of natural numbers, `sizeOf` is not the length, since it
also counts the elements, but it decreases when an element is removed. The
recursion of `bubbleSort` is structural, on the number of passes.

## Tests
-/

#eval bubble [4, 3, 5, 1, 2]                -- [3, 4, 1, 2, 5]
#eval bubble (bubble [4, 3, 5, 1, 2])       -- [3, 1, 2, 4, 5]
#eval bubbleSort [4, 3, 5, 1, 2] 5          -- [1, 2, 3, 4, 5]
#eval bubbleSort [10, 8, 2, 7, 3, 1] 6      -- [1, 2, 3, 7, 8, 10]

/-!
After the first pass on `[4, 3, 5, 1, 2]`, the largest element `5` is at the
end; after the second, the two largest elements `4` and `5` are.

## Specification

This section states the specification of bubble sort as theorems and concerns
only how the statements model it. The proofs are not discussed here. The
notation `~` and the predicates `List.Pairwise` and `IsSortedPairwise` are those
of `InsertSort.lean`, which this file imports.

### Permutations

The permutation part of the specification is `bubbleSort_perm`, for every
number `n` of passes. It rests on `bubble_perm`, the corresponding statement
for a single pass. The theorem `bubble_length` follows from `bubble_perm`, since
permutations have equal lengths.
-/

open List

theorem bubble_perm (l : List Nat) : bubble l ~ l := by sorry

theorem bubbleSort_perm (l : List Nat) (n : Nat) : bubbleSort l n ~ l := by sorry

theorem bubble_length (l : List Nat) : (bubble l).length = l.length := by sorry

/-!
### Sortedness

The sortedness part of the specification is `bubbleSort_sorted`. It states that
`n` passes sort a list of length `n`.
-/

theorem bubbleSort_sorted (l : List Nat) : IsSortedPairwise (bubbleSort l l.length) := by sorry

end SortingAlgorithms
