/-
Copyright (c) 2026 Iulian Simion. All rights reserved.
Released under the 3-Clause BSD License as described in the file LICENSE.
Authors: Iulian Simion, assisted by Claude (Anthropic) and Gemini (Google)
-/
import Lean
import Mathlib.Data.Nat.Basic

open Lean Elab Tactic

/-!
# Writing your own tactics

A macro (`08_Macros.lean`) rewrites syntax and cannot look at the
goal. A tactic written in `TacticM` can: it has access to the goal, the local
context, and the elaborator. Most of Lean's own tactics are written this way,
in Lean.


## Looking at the goal

The first tactic below reports the unsolved goals and the first target. The
type `TacticM` is a monad, so the code is written in `do` notation, and each
`←` runs one step and binds its result.
-/

inductive Even : ℕ → Prop where
  | zero : Even 0
  | add_two : ∀ k : ℕ, Even k → Even (k + 2)

def traceGoals : TacticM Unit :=
  do
    logInfo m!"Lean version {Lean.versionString}"
    logInfo "All goals:"
    let goals ← getUnsolvedGoals
    logInfo m!"{goals}"
    match goals with
    | [] => return
    | _ :: _ =>
      logInfo "First goal's target:"
      let target ← getMainTarget
      logInfo m!"{target}"

-- the command `elab` binds a piece of syntax to the code that implements it
elab "trace_goals" : tactic =>
  traceGoals

-- the tactic `trace_goals` changes no goal, so Mathlib's linter
-- `linter.unusedTactic` is switched off for this declaration
set_option linter.unusedTactic false in
theorem even_18_and_even_20 :
    Even 18 ∧ Even 20 :=
  by
    apply And.intro
    trace_goals    -- reports two goals and the first target
    all_goals sorry

/-!
## Example 1: reimplementing `assumption`

The tactic `hypothesis` below does what the built-in `assumption` tactic does:
walk the local context and close the goal with a hypothesis whose type
matches. It differs from `assumption` in one respect: it walks the context
forwards and takes the *first* matching hypothesis, while `assumption` walks it
backwards and takes the last.

The operations that make it work:

* `withMainContext` — run the body with the current goal's local context in
  scope; without it, the two operations below would not see the right
  hypotheses;
* `getLCtx` — the local context, as a list of declarations;
* `isDefEq a b` — are these two expressions the same up to computation? It is
  not a pure test: where one side contains a hole, `isDefEq` fills
  it in to make the two match, and that assignment sticks. This is what makes
  it usable for matching rather than only for comparing;
* `MVarId.assign goal e` — the goal is a hole; fill it with `e`.

The code below writes `LocalDecl.type ldecl` and `MVarId.assign goal …` in
full, naming the namespace of each operation; the usual forms are `ldecl.type`
and `goal.assign …`.

The `isImplementationDetail` check skips the auxiliary declarations Lean
inserts for its own bookkeeping, which are not hypotheses the user wrote.
-/

#check withMainContext

open Meta

def hypothesis : TacticM Unit :=
  withMainContext
    (do
      let target ← getMainTarget
      let lctx ← getLCtx
      for ldecl in lctx do
        if ! LocalDecl.isImplementationDetail ldecl then
          let eq ← isDefEq (LocalDecl.type ldecl) target
          if eq then
            let goal ← getMainGoal
            MVarId.assign goal (LocalDecl.toExpr ldecl)
            return
      failure)

elab "hypothesis" : tactic =>
  hypothesis

theorem hypothesis_example {α : Type} {p : α → Prop} {a : α} (hpa : p a) :
    p a :=
  by hypothesis

/-!
## Example 2: taking conjunctions apart

A call `destruct_and h` should close the goal whenever the goal is one of the
components of the conjunction `h`, at any depth. It is to replace the four
proofs below.
-/

theorem abc_a (a b c : Prop) (h : a ∧ b ∧ c) : a :=
  And.left h

theorem abc_b (a b c : Prop) (h : a ∧ b ∧ c) : b :=
  And.left (And.right h)

theorem abc_bc (a b c : Prop) (h : a ∧ b ∧ c) : b ∧ c :=
  And.right h

theorem abc_c (a b c : Prop) (h : a ∧ b ∧ c) : c :=
  And.right (And.right h)

/-!
The helper is a recursive search. Given a proof `hP` of some proposition `P`:
if `P` is the goal, use it; otherwise, if `P` is a conjunction, try the left
component and then the right one.
-/

partial def destructAndExpr (hP : Expr) : TacticM Bool :=
  withMainContext
    (do
      let target ← getMainTarget
      let P ← inferType hP
      let eq ← isDefEq P target
      if eq then
        let goal ← getMainGoal
        MVarId.assign goal hP
        return true
      else
        match Expr.and? P with
        | Option.none => return false
        | Option.some (_Q, _R) =>
          let hQ ← mkAppM ``And.left #[hP]
          let success ← destructAndExpr hQ
          if success then
            return true
          else
            let hR ← mkAppM ``And.right #[hP]
            destructAndExpr hR)

#check Expr.and?

def destructAnd (name : Name) : TacticM Unit :=
  withMainContext
    (do
      let h ← getFVarFromUserName name
      let success ← destructAndExpr h
      if ! success then
        failure)

elab "destruct_and" h:ident : tactic =>
  destructAnd (h.getId)

/-!
The tactic reproduces all four proofs:
-/

theorem abc_a_again (a b c : Prop) (h : a ∧ b ∧ c) : a :=
  by destruct_and h

theorem abc_b_again (a b c : Prop) (h : a ∧ b ∧ c) : b :=
  by destruct_and h

theorem abc_bc_again (a b c : Prop) (h : a ∧ b ∧ c) : b ∧ c :=
  by destruct_and h

theorem abc_c_again (a b c : Prop) (h : a ∧ b ∧ c) : c :=
  by destruct_and h

/-!
## What the tactic cannot do

The tactic has two limits.

**Only subterms.** `abc_bc_again` above works because `a ∧ b ∧ c` is
`a ∧ (b ∧ c)`, so `b ∧ c` is literally one of the parts the search walks
through. Had the hypothesis been `(a ∧ b) ∧ c`, the goal `b ∧ c` would not be
a subterm of it and the search would fail, even though the statement is
equally true.

**Only selection, never construction.** The goal `a ∧ c` below is true, but
proving it means *building* a new conjunction from two parts, and
`destructAndExpr` only ever selects an existing one. The commented-out proof
below fails.
-/

/-
theorem abc_ac (a b c : Prop) (h : a ∧ b ∧ c) : a ∧ c :=
  by destruct_and h   -- fails
-/

/-!
Further material: see the Further reading section of `../README.md`.
-/
