/-
Copyright (c) 2026 Iulian Simion. All rights reserved.
Released under the 3-Clause BSD License as described in the file LICENSE.
Authors: Iulian Simion, assisted by Claude (Anthropic) and Gemini (Google)
-/
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.Contrapose
import Mathlib.Tactic.Tauto
import Mathlib.Tactic.Push

/-! # Solutions — Classical logic -/

-- 1
theorem de_morgan (p q : Prop) : ¬(p ∨ q) → ¬p ∧ ¬q :=
  by
    intro h
    constructor
    · intro hp
      exact h (Or.inl hp)
    · intro hq
      exact h (Or.inr hq)

#print axioms de_morgan

-- 2
theorem dne_iff_lem : (∀ p : Prop, ¬¬p → p) ↔ (∀ p : Prop, p ∨ ¬p) :=
  by
    constructor
    · -- assume double negation elimination, prove excluded middle
      intro hdne p
      -- it suffices to rule out ¬(p ∨ ¬p)
      apply hdne
      intro hn
      -- from ¬(p ∨ ¬p) we get both ¬p and ¬¬p
      obtain ⟨hnp, hnnp⟩ := de_morgan p (¬p) hn
      exact hnnp hnp
    · -- assume excluded middle, prove double negation elimination
      intro hlem p hnnp
      obtain hp | hnp := hlem p
      · exact hp
      · exact absurd hnp hnnp

#print axioms dne_iff_lem

-- 3
theorem contrapositive (p q : Prop) : (¬q → ¬p) → (p → q) :=
  by
    intro h hp
    by_contra hq
    exact h hq hp

#print axioms contrapositive
