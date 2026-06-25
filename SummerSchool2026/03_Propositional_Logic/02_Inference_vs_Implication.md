# Logical Implication vs. Logical Inference

The distinction between logical implication and logical inference fundamentally comes down to the difference between a statement made *within* a formal system (the **object language**) and a claim made *about* that system (the **meta-language**).

### Logical Implication: A Connective

Implication (often denoted as $P \rightarrow Q$ or $P \implies Q$) is a logical connective used to build formulas. It takes two independent propositions and links them to form a new, compound proposition.

* **Nature:** It is a syntactic construct belonging strictly to the object language.
* **Evaluation:** An implication evaluates to a truth value based on the semantics of the system. In classical logic, $P \rightarrow Q$ is false if and only if $P$ is true and $Q$ is false.
* **Type Theory Perspective:** Under the Curry-Howard correspondence, implication is modeled simply as a function type. The proposition $P \rightarrow Q$ represents the *type* of a function that expects an argument of type $P$ and returns a term of type $Q$. It sits waiting to be used; it does not assert that $P$ is actually true.

### Logical Inference: A Deduction

Inference (often denoted with a turnstile, $P \vdash Q$) is the actual process or act of deriving a conclusion from premises using established rules of deduction.

* **Nature:** It is a meta-linguistic relation. When you write $P \vdash Q$, you are stepping outside the propositions themselves to assert that a valid proof exists leading from premise $P$ to conclusion $Q$.
* **Evaluation:** An inference does not have a "truth value." Instead, an inference is either *valid* or *invalid* depending on whether it strictly follows the axioms and inference rules (like Modus Ponens) of the chosen logical framework.
* **Proof Theory Perspective:** If you have established the premise $P$ (you possess a term of type $P$), and you apply an inference rule, you actively construct a proof of $Q$ (yielding a term of type $Q$). Inference is the computational step—the application of the function—often driven by tactics in interactive theorem proving.

### The Bridge: The Deduction Theorem

While distinct, implication and inference are tightly linked, most notably by the **Deduction Theorem**.

The theorem bridges the meta-language and the object language by stating that if you can validly infer $Q$ assuming $P$ as a premise ($P \vdash Q$), then the implication $P \rightarrow Q$ is provable as a theorem within an empty context ($\vdash P \rightarrow Q$).

Conversely, the rule of Modus Ponens acts as the bridge in the opposite direction: from the established premise $P$ and the implication $P \rightarrow Q$, you can infer $Q$ ($P, P \rightarrow Q \vdash Q$).

---
Copyright (c) 2026 Iulian Simion. All rights reserved.
Released under the 3-Clause BSD License as described in the file LICENSE.txt.
Authors: Iulian Simion

Note: This file was synthesized with the assistance of Gemini 3.1 Pro.