# Morning session — algorithms

An algorithm is written as a Lean function. Each file of the first part gives
the **implementation**, **tests** evaluated with `#eval`, and a
**specification**: a proposition about the output for every input. Except in
the files on sorting, `07` and `08`, a proof shows that the implementation
satisfies it. The second part counts the steps of these algorithms, proves a
closed form or an upper bound for their number, and states its class in big-O
notation.

The files are Lean modules of the library `Algorithms`, in the folder
[`Algorithms/`](Algorithms/). 

## Correctness

| # | File | Contents | Solutions |
| :--- | :--- | :--- | :--- |
| 01 | [`MaxList.lean`](Algorithms/MaxList.lean) | The maximum of a list: implementation, tests, specification. The inductive type `List` and the notation `x :: xs`; structural recursion; `List.Mem` as an inductive predicate; structural induction on lists; `#print axioms`; `Option` and other implementations, including `List.max?` and `List.max` of Lean core and `List.maximum` of Mathlib. | [solutions](Algorithms/solutions/MaxList.lean) |
| 02 | [`MaxVect.lean`](Algorithms/MaxVect.lean) | The maximum of a vector. The type `List.Vector Nat n` of lists of length `n`; recursion and induction on the length; other implementations, and the type `Vector` of Lean core. | [solutions](Algorithms/solutions/MaxVect.lean) |
| 03 | [`XorCipher.lean`](Algorithms/XorCipher.lean) | The XOR cipher on bytes. The type `UInt8`; exclusive or; the round-trip property; the tactic `bv_decide` and the axiom it adds; a `calc` chain. | [solutions](Algorithms/solutions/XorCipher.lean) |
| 04 | [`AffineCipher.lean`](Algorithms/AffineCipher.lean) | The affine cipher. Multiplicative inverses modulo 256; a structure with a field that is a proof; tests as `example`s proved by `rfl`. | [solutions](Algorithms/solutions/AffineCipher.lean) |
| 05 | [`ToBits.lean`](Algorithms/ToBits.lean) | Binary representation. Well-founded recursion and termination; irreducible definitions; a recursive proof as strong induction; other implementations with an error, and the functions of Lean core and Mathlib for digits. | [solutions](Algorithms/solutions/ToBits.lean) |
| 06 | [`BinaryExp.lean`](Algorithms/BinaryExp.lean) | Exponentiation by squaring. Induction with `generalizing`; the correctness of the complete algorithm from two specifications. | [solutions](Algorithms/solutions/BinaryExp.lean) |
| 07 | [`InsertSort.lean`](Algorithms/InsertSort.lean) | Insertion sort. The specification of sorting: sortedness with `List.Pairwise`, permutations with `List.Perm`. | — |
| 08 | [`BubbleSort.lean`](Algorithms/BubbleSort.lean) | Bubble sort. Passes over the list; well-founded recursion on lists; the specification of sorting for a number of passes. | — |
| 09 | [`BinarySearchTree.lean`](Algorithms/BinarySearchTree.lean) | Search in a binary search tree. `BinaryTree`; the inductive predicates `Mem` and `IsBST`; soundness and completeness of the search; the axioms of proofs with `simp` and with `simp only`. | [solutions](Algorithms/solutions/BinarySearchTree.lean) |

## Time complexity

The files of this part are in the folder
[`Algorithms/TimeComplexity/`](Algorithms/TimeComplexity/).

| # | File | Contents | Solutions |
| :--- | :--- | :--- | :--- |
| 10 | [`Asymptotics.lean`](Algorithms/TimeComplexity/Asymptotics.lean) | Big-O notation with Mathlib's `IsBigO` and the filter `atTop`; growth rates; bounds from known bounds; constants and thresholds; bounds for functions defined by recursion, including a strengthened induction hypothesis and a recursion that halves. | [solutions](Algorithms/solutions/TimeComplexity/Asymptotics.lean) |
| 11 | [`MaxList.lean`](Algorithms/TimeComplexity/MaxList.lean) | The type `TimeM` of CSLib and the cost model; the cost of the maximum of a list as a closed form; the class `O(n)`. | [solutions](Algorithms/solutions/TimeComplexity/MaxList.lean) |
| 12 | [`MaxVect.lean`](Algorithms/TimeComplexity/MaxVect.lean) | The cost of the maximum of a vector. | — |
| 13 | [`XorCipher.lean`](Algorithms/TimeComplexity/XorCipher.lean) | The cost of the XOR cipher; a cost proof written as a `calc` chain. | — |
| 14 | [`AffineCipher.lean`](Algorithms/TimeComplexity/AffineCipher.lean) | The cost of the affine cipher. | — |
| 15 | [`ToBits.lean`](Algorithms/TimeComplexity/ToBits.lean) | The cost of the binary representation, `Nat.log2 n + 1`; the class `O(log n)`. | — |
| 16 | [`BinaryExp.lean`](Algorithms/TimeComplexity/BinaryExp.lean) | The cost of exponentiation by squaring, from the cost of the binary representation; functions that agree eventually. | — |
| 17 | [`InsertSort.lean`](Algorithms/TimeComplexity/InsertSort.lean) | An upper bound `n ^ 2` for insertion sort, whose cost depends on the order of the input. | — |
| 18 | [`BinarySearchTree.lean`](Algorithms/TimeComplexity/BinarySearchTree.lean) | The cost of search is at most the height of the tree; perfect trees; the class `O(log N)`. | — |

## Specification and cost

Each algorithm of the first part except bubble sort is treated again in the
second part.

|           | Correctness, files `01`–`09`                    | Time complexity, files `10`–`18`                          |
| :-------- | :---------------------------------------------- | :--------------------------------------------------- |
| function  | the implementation, returning the result        | the same function with result type `TimeM ℕ α`, a pair of a result and a cost |
| statement | a property of the result for every input        | a closed form or an upper bound of the cost, and its class in `O(·)` |
| proof     | induction along the recursion of the function   | the same induction, on the cost                      |

The first exercise of `TimeComplexity/MaxList.lean` proves that the result in
this pair, the field `ret`, is the result of the implementation of the first
part.

## Building

The folder `day-4/algorithms/` is a Lake project that depends on Mathlib and
CSLib. From `day-4/algorithms/`,
`lake exe cache get` downloads the compiled Mathlib, and `lake build` compiles
all files, including the solutions.

## Further reading

| Source | How it extends this session |
| :--- | :--- |
| [Functional Programming in Lean](https://lean-lang.org/functional_programming_in_lean/) | Lean as a programming language: structures, `Option`, type classes, monads and `do` notation. The background for the implementations of `01`–`09` and for `TimeM` in `11`–`18`. |
| [Theorem Proving in Lean 4](https://lean-lang.org/theorem_proving_in_lean4/) | [Induction and Recursion](https://lean-lang.org/theorem_proving_in_lean4/Induction-and-Recursion/) explains structural and well-founded recursion, the two kinds of definition in `05` and `08`, and how Lean justifies them. |
| [The Hitchhiker's Guide to Logical Verification](https://github.com/lean-forward/logical_verification_2026) | A one-semester course that verifies functional programs in Lean, with inductive predicates as in `01` and `09`. |
| T. H. Cormen, C. E. Leiserson, R. L. Rivest, C. Stein, *Introduction to Algorithms*, 4th edition, MIT Press, 2022 | The standard textbook on algorithms. Insertion sort in Chapter 2, asymptotic notation in Chapter 3, binary search trees in Chapter 12. |
| [Mathlib documentation](https://leanprover-community.github.io/mathlib4_docs/) | The definitions and lemmas behind `10`: `Asymptotics.IsBigO`, the filter `Filter.atTop`, and `Real.log`. |
| [CSLib](https://github.com/leanprover/cslib) | The library that provides `TimeM`. Its documentation of `TimeM` cites N. A. Danielsson, *Lightweight Semiformal Time Complexity Analysis for Purely Functional Data Structures*, POPL 2008, for the method of counting ticks. |
