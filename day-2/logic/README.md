# Morning session — propositions and the logical connectives

Three hours, with a break after `02`. The timings, the reasons for the order
and the teaching notes are in [`session-plan.md`](session-plan.md).

Throughout the session, a proposition is a type, and a proof of it is a term of
that type. A proof of `p → q` is a function from proofs of `p` to proofs of
`q`; this is the Curry–Howard correspondence.

Each presentation file ends with three exercises, whose solutions are in
`solutions/`. Further exercises are collected in `07`.

| # | File | Contents | Solutions |
| :--- | :--- | :--- | :--- |
| 01 | [`01_Propositions.lean`](01_Propositions.lean) | Equality as a type, and the declaration of `Eq`; `rfl` and definitional equality; applying a theorem like a function, and rewriting with `rw`; a goal as a context and a target; `True` and `False`; `def`, `theorem` and `example`; `sorry`. | [solutions](solutions/01_Propositions.lean) |
| 02 | [`02_Implication_and_Universal.lean`](02_Implication_and_Universal.lean) | `→` as the type of functions between proofs, and `∀` as its dependent form. Each in the target (`intro`, `fun`) and in the context (`apply`, `have`, application); proofs written as terms and in tactic mode (`by`, `exact`). | [solutions](solutions/02_Implication_and_Universal.lean) |
| 03 | [`03_Conjunction_Disjunction_Equivalence.lean`](03_Conjunction_Disjunction_Equivalence.lean) | `∧`, `∨` and `↔`, each in the target (`constructor`, `left`, `right`, `⟨_, _⟩`) and in the context (projections, `obtain`, `rw`); a disjunction with three cases. | [solutions](solutions/03_Conjunction_Disjunction_Equivalence.lean) |
| 04 | [`04_Existential_and_Negation.lean`](04_Existential_and_Negation.lean) | `∃` in the target (`use`, `⟨a, ha⟩`) and in the context (`obtain`); unique existence; `False` and `exfalso`; `¬p` as `p → False`, in the target (`intro`) and in the context (application, `contradiction`); `push Not`; a proof that no natural number squares to 2. | [solutions](solutions/04_Existential_and_Negation.lean) |
| 05 | [`05_Classical_Logic.lean`](05_Classical_Logic.lean) | `#print axioms`; the law of excluded middle and case analysis on a proposition; the tactics `by_cases`, `by_contra`, `contrapose`, `push Not` past `∀` and `tauto`; excluded middle, double negation elimination, proof by contradiction and Peirce's law as forms of one principle; the axiom of choice, from which excluded middle is derived by Diaconescu's theorem, with `choose` and `classical`. | [solutions](solutions/05_Classical_Logic.lean) |
| 06 | [`06_Prop_vs_Bool.lean`](06_Prop_vs_Bool.lean) | `Bool` against `Prop`, and the coercion of `b` to `b = true`; `Decidable` and `decide`; how `rfl`, `decide` and `norm_num` each prove `2 + 2 = 4`, and which of them works over `ℝ`. | [solutions](solutions/06_Prop_vs_Bool.lean) |
| 07 | [`07_Exercises.lean`](07_Exercises.lean) | Further exercises: one section per topic file `01`–`06`. | [solutions](solutions/07_Exercises.lean) |

## Target and context

For each open goal, the Infoview shows the hypotheses, the **context**, above
`⊢`, and the statement still to be proved, the **target**, below it. Files
`02`–`04` treat each connective and quantifier both in the target and in the
context, and fill in this table for it:

| Connective or quantifier | TARGET, below `⊢`                                            | CONTEXT, above `⊢`                                          |
| :----------------------- | :----------------------------------------------------------- | :---------------------------------------------------------- |
| any                      | how to *construct* a proof of it: the **introduction** rules | how to *use* a given proof of it: the **elimination** rules |

A term written directly and a sequence of tactics both produce a proof term.
Tactic mode builds the term step by step, and the Infoview shows the goal after
each step.


## Further reading



| Source | How it extends this session |
| :--- | :--- |
| [Theorem Proving in Lean 4](https://lean-lang.org/theorem_proving_in_lean4/) | The canonical treatment of everything here. [Propositions and Proofs](https://lean-lang.org/theorem_proving_in_lean4/propositions_and_proofs.html) covers `01`–`03` with more connectives and more term-mode detail; Quantifiers and Equality covers `04`; [Axioms and Computation](https://lean-lang.org/theorem_proving_in_lean4/axioms_and_computation.html) is the long form of `05`, including why `Classical.choice` forces `noncomputable`. |
| [Mathematics in Lean](https://leanprover-community.github.io/mathematics_in_lean/) | The applied counterpart. [Logic](https://leanprover-community.github.io/mathematics_in_lean/C03_Logic.html) redoes the same connectives and quantifiers on ε–δ statements about the reals, which is where nested `∀`/`∃` first becomes hard. Work through it in a Lean file, not in the browser. |
| [The Hitchhiker's Guide to Logical Verification](https://github.com/lean-forward/logical_verification_2026) | A one-semester course with the same starting point. Chapter 3 gives the introduction and elimination rules as a table; Chapter 12 treats the peculiarities of `Prop` behind `06`, including proof irrelevance. |
| [Logic and Proof](https://leanprover-community.github.io/logic_and_proof/) | Logic first, then the same rules in Lean 4. Chapters 3 and 8 give natural deduction for propositional and first-order logic, the introduction and elimination rules of `02`–`04`; Chapters 4 and 9 do them in Lean; Chapter 5 is classical reasoning, as in `05`. |