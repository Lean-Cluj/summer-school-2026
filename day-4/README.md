# Day 4

## Morning session — algorithms

Algorithms written as Lean functions, with tests, specifications and proofs of
correctness: the maximum of a list and of a vector, two ciphers on bytes,
binary representation and exponentiation by squaring, two sorting algorithms,
and search in binary search trees. The second part introduces big-O notation
from Mathlib and proves bounds on the number of steps of the same algorithms,
counted with the type `TimeM` of the library CSLib.

[Session page](algorithms/README.md)

## Afternoon session — Aeneas

The tool Aeneas translates Rust programs into Lean definitions. The session
translates small Rust crates and proves specifications of the generated
definitions: addition with overflow, an enumeration, error codes, addition
modulo the prime `2 ^ 31 - 1`, and loops over arrays, among them the XOR and
affine ciphers of the morning.

[Session page](aeneas/README.md)
