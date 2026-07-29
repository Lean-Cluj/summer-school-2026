/-
Copyright (c) 2026 Iulian Simion. All rights reserved.
Released under the 3-Clause BSD License as described in the file LICENSE.txt.
Authors: Iulian Simion

Note: This file contains examples and text adapted from the "Hitchhiker's
Guide to Logical Verification" (Copyright 2018–2026 Anne Baanen et al.),
which is also used under the 3-Clause BSD License.
-/
import Lean
import Mathlib.Data.Nat.Basic

open Lean Elab Tactic

/-
  EXAMPLE: the following example is from
  Hitchhiker's Guide to Logical Verification
  by Anne Baanen, Alexander Bentkamp, Jasmin Blanchette, Johannes Hölzl, Jannis Limperg
  Chapter 8 Metaprogramming
-/

inductive Even : ℕ → Prop where
  | zero    : Even 0
  | add_two : ∀k : ℕ, Even k → Even (k + 2)

def traceGoals : TacticM Unit :=
  do
    logInfo m!"Lean version {Lean.versionString}"
    logInfo "All goals:"
    let goals ← getUnsolvedGoals
    logInfo m!"{goals}"
    match goals with
    | []     => return
    | _ :: _ =>
      logInfo "First goal's target:"
      let target ← getMainTarget
      logInfo m!"{target}"

elab "trace_goals" : tactic =>
  traceGoals

theorem Even_18_and_Even_20 (α : Type) (a : α) :
  Even 18 ∧ Even 20 :=
  by
    apply And.intro
    trace_goals
    · sorry --intro_and_even
    · sorry


/-
  EXAMPLE: the following example is from
  Hitchhiker's Guide to Logical Verification
  by Anne Baanen, Alexander Bentkamp, Jasmin Blanchette, Johannes Hölzl, Jannis Limperg
  Chapter 8 Metaprogramming
-/
/- ## First Example: An Assumption Tactic

We define a `hypothesis` tactic that behaves essentially the same as the
predefined `assumption` tactic. -/

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

theorem hypothesis_example {α : Type} {p : α → Prop} {a : α}
    (hpa : p a) :
  p a :=
  by hypothesis


/- ## Second Example: A Conjunction-Destructing Tactic

We define a `destruct_and` tactic that automates the elimination of `∧` in
premises, automating proofs such as these: -/

theorem abc_a (a b c : Prop) (h : a ∧ b ∧ c) :
  a :=
  And.left h

theorem abc_b (a b c : Prop) (h : a ∧ b ∧ c) :
  b :=
  And.left (And.right h)

theorem abc_bc (a b c : Prop) (h : a ∧ b ∧ c) :
  b ∧ c :=
  And.right h

theorem abc_c (a b c : Prop) (h : a ∧ b ∧ c) :
  c :=
  And.right (And.right h)

/- Our tactic relies on a helper function, which takes as argument the
hypothesis `h` to use as an expression: -/

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
         | Option.none        => return false
         | Option.some (Q, R) =>
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

/- Let us check that our tactic works: -/

theorem abc_a_again (a b c : Prop) (h : a ∧ b ∧ c) :
  a :=
  by destruct_and h

theorem abc_b_again (a b c : Prop) (h : a ∧ b ∧ c) :
  b :=
  by destruct_and h

theorem abc_bc_again (a b c : Prop) (h : a ∧ b ∧ c) :
  b ∧ c :=
  by destruct_and h

/- This is successful because `a ∧ b ∧ c` is grouped as `a ∧ (b ∧ c)`.
   Why would it fail on `(a ∧ b) ∧ c`? -/

theorem abc_c_again (a b c : Prop) (h : a ∧ b ∧ c) :
  c :=
  by destruct_and h

/-
theorem abc_ac (a b c : Prop) (h : a ∧ b ∧ c) :
  a ∧ c :=
  by destruct_and h   -- fails
-/


/-
  TODO: `extra`
  Example form mechanics of proof

  via macros?
  https://github.com/hrmacbeth/math2001/blob/main/Library/Tactic/Extra/Basic.lean
-/
