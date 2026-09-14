# Afternoon session — calculation and proof principles

In the [morning](../logic/README.md), the logical shape of the goal decided which rule to apply. In
this session, the tactic is chosen by the mathematics instead: `ring` for a
polynomial identity, `omega` for linear arithmetic over `ℕ` and `ℤ`,
`induction` for a statement about every natural number.

Each presentation file ends with its exercises, three per topic (two in `07`,
one in `08`), whose solutions are in `solutions/`; `07` and `08` share one
solution file. Further exercises are collected in `09`.

| # | File | Contents | Solutions |
| :--- | :--- | :--- | :--- |
| 01 | [`01_Rewriting.lean`](01_Rewriting.lean) | `rewrite`, and `rw` as `rewrite` followed by a restricted `rfl`; `rw` with a hypothesis or a library lemma, with a list of equations, reversed (`←`), in a hypothesis (`at`), at one occurrence (`nth_rw`), and `rwa`; finding a lemma with the naming conventions, `exact?`, `apply?`, `rw?`, Loogle, LeanSearch and LeanExplore. | [solutions](solutions/01_Rewriting.lean) |
| 02 | [`02_Calculation.lean`](02_Calculation.lean) | `ring` for identities that follow from the commutative ring axioms, and `field_simp` for denominators; `norm_num` for numerals; `calc` chains; `have` for an intermediate fact. | [solutions](solutions/02_Calculation.lean) |
| 03 | [`03_Inequalities_and_Congruences.lean`](03_Inequalities_and_Congruences.lean) | Chains of inequalities; `rel`, `gcongr`, `positivity` and `linarith`; congruences (`Int.ModEq`) and chains of them; `omega`; truncated subtraction on `ℕ`; coercions, `push_cast` and `norm_cast`. | [solutions](solutions/03_Inequalities_and_Congruences.lean) |
| 04 | [`04_Cases.lean`](04_Cases.lean) | `cases` on a `Bool`, on a `Nat` and on a disjunction, including nested ones; `rcases` and `obtain`; `<;>` and `all_goals`; `fin_cases`; `interval_cases`. | [solutions](solutions/04_Cases.lean) |
| 05 | [`05_Induction.lean`](05_Induction.lean) | Induction on `ℕ`: `2 ^ n ≥ n + 1`, positive powers of a positive rational, Bernoulli's inequality; definitions by recursion and `show`; two-step induction (`Nat.twoStepInduction`); strong induction (`Nat.strong_induction_on`); induction on `List`. | [solutions](solutions/05_Induction.lean) |
| 06 | [`06_Stronger_Tactics.lean`](06_Stronger_Tactics.lean) | The search tactics `simp`, `nlinarith`, `grind` and `aesop`; when their proofs are classical; a search compared with a chain. | [solutions](solutions/06_Stronger_Tactics.lean) |
| 07 | [`07_Tactic_Combinators.lean`](07_Tactic_Combinators.lean) | The combinators `repeat'`, `first`, `all_goals`, `try`, `any_goals`, `solve` and `<;>`, on one running example. | [solutions](solutions/07_Combinators_and_Macros.lean), shared with `08` |
| 08 | [`08_Macros.lean`](08_Macros.lean) | Macros: a macro for a term, `syntax` with `macro_rules`, a macro for a tactic, and macros for operators. | as `07` |
| 09 | [`09_Exercises.lean`](09_Exercises.lean) | Further exercises: one section per topic file `01`–`06`, and section 7 for `07` and `08`. | [solutions](solutions/09_Exercises.lean) |

The [appendix](appendix/README.md) has two optional files that follow on
from this session: writing tactics in Lean, and the maintenance tools
`#lint`, `#min_imports` and `simp?`.

## Further reading


| Source | How it extends this session |
| :--- | :--- |
| [The Mechanics of Proof](https://hrmacbeth.github.io/math2001/) | The closest match to this session's style, and the source of the `calc`-and-`rel` habit in `02` and `03`. Chapters 1–2 build calculational proofs from scratch, inequalities included (§1.4); [Chapter 6](https://hrmacbeth.github.io/math2001/06_Induction.html) covers induction, including the two-step and strong forms of `05`. Written for undergraduates with no prior Lean. |
| [Mathematics in Lean](https://leanprover-community.github.io/mathematics_in_lean/) | The next step up, on real mathematics. [Basics](https://leanprover-community.github.io/mathematics_in_lean/C02_Basics.html) extends `01` and `02` — `rw`, `ring`, `linarith` and `calc` — and later chapters apply them to sets, functions and analysis. |
| [Theorem Proving in Lean 4](https://lean-lang.org/theorem_proving_in_lean4/) | [Tactics](https://lean-lang.org/theorem_proving_in_lean4/tactics.html) is the reference for `04` and `07`, including combinators. Induction and Recursion explains what `induction` actually does, and where the recursors of `05` come from. |
| [Logic and Proof](https://leanprover-community.github.io/logic_and_proof/) | Chapters 17–18 treat the natural numbers, definitions by recursion and proof by induction, first on paper and then in Lean, as in `05`. |
| [Mathlib tactic reference](https://leanprover-community.github.io/mathlib4_docs/tactics.html) and the [Lean Language Reference](https://lean-lang.org/doc/reference/latest/Tactic-Proofs/) | The full list, for when a tactic in `06` does not do what you expected. Every tactic used today is documented with its options. |
| [Mathlib naming conventions](https://leanprover-community.github.io/contribute/naming.html) | Extends the naming discussion in `01`. Once the conventions are internalised you can often guess a lemma name before searching for it. |
| [Metaprogramming in Lean 4](https://leanprover-community.github.io/lean4-metaprogramming-book/) | The continuation of `08` and of [`appendix/01_Writing_Tactics.lean`](appendix/01_Writing_Tactics.lean): `Syntax`, `Expr`, elaboration, and writing real tactics. |
| [Functional Programming in Lean](https://lean-lang.org/functional_programming_in_lean/) | Lean as a programming language. Useful background for `08` and the appendix, where the proofs are programs. |
