/-
Copyright (c) 2026 Iulian Simion. All rights reserved.
Released under the 3-Clause BSD License as described in the file LICENSE.txt.
Authors: Iulian Simion
-/
import Mathlib.Tactic.Linarith

/-
  # Implication connective

  The implication connective `→` constructs the type of a function
  that takes the witness of `p` and produces a witness of `q`.
-/

section

variable (p q : Prop)

#check (p → q)

variable (hp : p) (i : p → q)

#check (i hp)
-- #eval (i hp)

end

/-
  # Second-Order Logic perspective

  Here we think of propositions as variables that can be quantified over.

  ## Implication in TARGET

  When the target consists of an implication `p → q`,
  we are *constructing* a function which maps the witness `hp` (proof-term of `p`,
  hypothesis that `p` is true) to a witness `hq` of `q`.

  ### Forward Reasoning (The raw functional programming way):
-/

example (p q : Prop) : p → q :=
  fun (hp : p) => sorry

example (p q : Prop) : p → q → p :=
  fun (hp : p) => (fun _ => hp)

/-
  ### Backward Reasoning (The tactic way):

  Taking a proof of `p` and returning a proof of `q` is
  the same as assuming `p` is true (i.e. it is in the context) and proving `q`.

  The `intro` tactic adds the witness `hp : p` as a variable `hp` to the local context
  and changes the target to `q`. We can then use the hypothesis `hp` to prove `q`.
-/

example (p q : Prop) : p → q :=
  by
    intro hp
    sorry

example (p q : Prop) : p → q → p :=
  by
    intro hp hq
    exact hp

/-
  ## Implication in CONTEXT

  When an implication is present in the context, we *consume* it by applying it like any function.

  ### Forward Reasoning (The raw functional programming way):
-/

example (p q : Prop) (hp : p) (hpq : p → q) : q :=
  hpq hp

/-
  ### Backward Reasoning (The tactic way):
-/

example (p q : Prop) (hp : p) (hpq : p → q) : q :=
  by
    have hq : q := hpq hp
    exact hq

/-
  Example (see [Hitch] Sections 3.1 and 3.2)
-/

theorem modus_ponens (p q : Prop) :
  (p → q) → p → q :=
  by
    intro hpq hp
    apply hpq
    exact hp

/-
  # First-Order Logic perspective

  Here, the implication connective `→` links `concrete` statements,
  e.g., statements about numbers.

  ## Implication in TARGET

  When the target consists of an implication, we are constructing a function.

  ### Forward reasoning

  Constructing such a function means expressing this function in terms of
  the axioms of the formal system and things that derive from these axioms.

  In our first example, we make use of Congruence of Arguments:
  given a function `f`, if `x = y` then `f x = f y`.
-/

example (n m : Nat) : (n = m) → (n + 1 = m + 1) :=
  fun (h : n = m) => congrArg (fun (x : Nat) => x + 1) h

/-
  The next example uses intermediate results to construct the function:
    - transitivity of equality
    - the injectivity of the constructors of inductive types, in particular of `Nat`.
-/

example (n : Nat) : n = 0 → 1 ≠ n :=
  fun (h0 : n = 0) => fun (h1 : 1 = n) => Nat.noConfusion (Eq.trans h1 h0)

/-
  Forward reasoning requires discipline in arranging the context in an expression
  that is a valid proof of the target.

  Manipulating the context in this way, following strict rules of functional programming,
  is draining the focus from the actual proof to the syntax of the proof.

  ### Backward Reasoning

  Tactics mode gives access to the context in a more natural way,
  and gives us tools to automate parts of the proof.
-/

example (n : Nat) : 2 < n → 1 < n :=
  fun (h : n > 2) => Nat.lt_of_le_of_lt (Nat.le_succ 1) h

-- vs

example (n : Nat) : 2 < n → 1 < n :=
  fun (h : n > 2) => by linarith

example (n m : Nat) : (n = m) → (n + 1 = m + 1) :=
  fun (hA : n = m) => congrArg (fun (x : Nat) => x + 1) hA

-- vs

example (n m : Nat) : (n = m) → (n + 1 = m + 1) :=
  fun (hA : n = m) => by linarith

-- or

example (n m : Nat) : (n = m) → (n + 1 = m + 1) :=
  by
    intro _
    linarith

/-
  ## Implication in CONTEXT

  When an implication is present in the context, we *consume* it by applying it like any function.

  ### Forward vs Backward Reasoning

  Often, forward and backward reasoning are used together in a single proof.
-/

example (n m : Nat) (h₁ : n = 11) (h₂ : n > 7 → m > 2) : m > 2 :=
  h₂ (by linarith)

-- vs

example (n m : Nat) (h₁ : n = 11) (h₂ : n > 7 → m > 2) : m > 2 :=
  by
    have h₃ : n > 7 := by linarith
    exact h₂ h₃
