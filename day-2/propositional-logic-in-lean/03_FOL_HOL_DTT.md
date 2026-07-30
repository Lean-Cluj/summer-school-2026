# First-Order Logic (FOL)
**What it does**: Allows quantification only over base objects (individuals).

**Boundary**: You can say "for all numbers x," but you cannot say "for all properties P."

**Analogy**: A calculator that can only compute with the numbers you type in, but cannot take a formula as an input.

# Second-Order Logic (SOL)

**What it does:** Extends FOL by allowing quantification over properties, relations, and sets of base objects, in addition to the objects themselves.

**Boundary:** You can say "for all properties P of individuals," but you cannot say "for all properties of properties." It introduces exactly one layer of abstraction above the base data, strictly forbidding you from nesting those abstractions any further.

**Analogy:** A calculator that allows you to input and evaluate formulas over groups of numbers, but the formulas themselves cannot accept other formulas as inputs.

# Higher-Order Logic (HOL)
**What it does**: Extends both FOL and SOL by removing the restriction on layers of abstraction. It allows quantification not just over base objects (like FOL) or properties of objects (like SOL), but over properties of properties, functions of functions, and so on, up to any arbitrary, finite order.

**Boundary**: You can say "for all properties of properties," but you still maintain a strict, uncrossable wall between your data (terms) and your categories (types). A category or type cannot depend on a specific piece of data.

**Analogy**: A fully recursive programmable calculator where formulas can accept formulas, which can accept other formulas as inputs. However, the underlying hardware architecture defining the fundamental difference between "data" and "formulas" remains rigidly fixed.

# Dependent Type Theory (DTT)
**What it does**: Includes the expressive power of HOL, but shatters the wall between terms and types. Types can now depend directly on data values.

**Boundary**: The boundary between data and categories is fundamentally erased. Instead of just adding logic on top, DTT completely rebuilds it using the Curry-Howard correspondence. A "proposition" is treated exactly as a type, and a "quantifier" becomes a dependent function.

**Analogy**: A system where the software can rewrite its own hardware architecture on the fly depending on the data it is currently processing.


      _______________________________________________________
     /                                                       \
    |               Dependent Type Theory (DTT)               |
    |                                                         |
    |       ___________________________________________       |
    |     /                                             \     |
    |    |             Higher-Order Logic (HOL)          |    |
    |    |                                               |    |
    |    |        _______________________________        |    |
    |    |      /                                 \      |    |
    |    |     |     Second-Order Logic (SOL)      |     |    |
    |    |     |                                   |     |    |
    |    |     |        _____________________      |     |    |
    |    |     |      /                       \    |     |    |
    |    |     |     |   First-Order Logic     |   |     |    |
    |    |     |     |         (FOL)           |   |     |    |
    |    |     |      \_______________________/    |     |    |
    |    |     |                                   |     |    |
    |    |      \_________________________________/      |    |
    |    |                                               |    |
    |     \_____________________________________________/     |
    |                                                         |
     \_______________________________________________________/

---
Copyright (c) 2026 Iulian Simion. All rights reserved.
Released under the 3-Clause BSD License as described in the file LICENSE.txt.
Authors: Iulian Simion

Note: This file was synthesized with the assistance of Gemini 3.1 Pro.