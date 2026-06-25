/-
Copyright (c) 2026 Iulian Simion. All rights reserved.
Released under the 3-Clause BSD License as described in the file LICENSE.txt.
Authors: Iulian Simion
-/
import Mathlib.Data.Real.Basic

/-
  # APPLY

  The `apply` tactic works backwards on arrows,
  it is used for structural reverse-engineer.

  # apply for functions:
-/

def f : ℤ → ℤ := fun x => x+1
def g : ℤ → ℤ := fun x => x^2


def h : ℤ → ℤ := by
  intro x   -- Context now has `x : Nat`, Goal becomes `⊢ Nat`
  apply f   -- Goal becomes `⊢ Nat` (the required argument for f)
  apply g   -- Goal becomes `⊢ Nat` (the required argument for g)
  exact x   -- Closes the goal by providing x

-- equivalent to

def h_fun : ℤ → ℤ := fun x => f (g x)

-- equivalent to

def h_term : ℤ → ℤ := f ∘ g

#eval h 4
#eval h_fun 4
#eval h_term 4

/-
  EXERCISE:
  Define the function ℚ → ℚ  h(x)= 1/(x-1)
-/
def ff : ℚ → ℚ := fun x => 1/x
def gg : ℚ → ℚ := fun x => x-1

def hh_term : ℚ → ℚ := ff ∘ gg

-- division by zero
#eval hh_term 1


/-
  # apply for implications

  Implications `p → q` are functions,
  from the proof term of `p` to the proof term of `q`
-/
#check le_trans
example (x y z : ℝ) (h₀ : x ≤ y) (h₁ : y ≤ z) : x ≤ z := by
  apply le_trans
  · apply h₀
  · apply h₁

-- or

example (x y z : ℝ) (h₀ : x ≤ y) (h₁ : y ≤ z) : x ≤ z := le_trans h₀ h₁


example (k a b : Nat) (ha : k ∣ a) (hb : k ∣ b) : k ∣ (a + b) := by
  apply Nat.dvd_add
  · exact ha  -- Solves Goal 1: ⊢ k ∣ a
  · exact hb  -- Solves Goal 2: ⊢ k ∣ b

example (x y : ℝ) (hx : 0 < x) (hy : 0 < y) : 0 < x * y := by
  apply mul_pos
  · exact hx  -- Solves Goal 1: ⊢ 0 < x
  · exact hy  -- Solves Goal 2: ⊢ 0 < y

/-
  EXERCISE:
  Using `mul_nonneg` and `sq_nonneg`
  construct a proof-term for the following statement.
  Can you do it in one line?
-/
example (x : ℝ) : 0 ≤ 3 * (x+1)^2 := by
  apply mul_nonneg
  · norm_num
  · apply sq_nonneg (x + 1)

/-
  # REWRITE

  The `rewrite` tactic is a find-and-replace tool.
  It works with equalities (`=`) and equivalences (`↔`).
-/
example (a b c : ℝ) : (a * b) * c = b * (a * c) :=
  by
    rewrite [mul_comm a b]
    rewrite [mul_assoc b a c]
    rfl
/-
  It is most commonly used in the form of `rw`
  which also applies a `rfl` after `rewrite`
-/
example (a b c : ℝ) : (a * b) * c = b * (a * c) :=
  by
    rw [mul_comm a b]
    rw [mul_assoc b a c]

/-
  whereas `rw` rewriets all instances that match the pattern,
  `nth_rw` allows you to rewrite the n-th occurence.
-/
example (a b c : Nat) (h : a + b = c) : (a + b) * (a + b) = a * c + b * c :=
  by
    nth_rw 2 [h]
    rw [add_mul]

/-
  EXERCISE
  Using `rw` with `mul_add` and `mul_comm`
  construct a proof-term for the following statement.
-/
example (a b c : ℝ) : a * (b + c) = b * a + c * a  :=
  by
    rw [mul_add]
    rw [mul_comm a b]
    rw [mul_comm a c]
