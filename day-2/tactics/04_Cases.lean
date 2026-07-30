/-
Copyright (c) 2026 Iulian Simion. All rights reserved.
Released under the 3-Clause BSD License as described in the file LICENSE.txt.
Authors: Iulian Simion
-/
import Mathlib.Data.Nat.Basic
import Mathlib.Tactic

/-
  # CASES
  Both `cases` and `match` are used to deconstruct inductive types
  (like `Nat` or `List`)


  When you call `cases x`, the tactic looks at the local context,
  replaces every instance of `x` with its respective constructors,
  and generates a new subgoal for each constructor.
-/

example (b : Bool) : b = true ∨ b = false := by
  cases b
  case false =>
    right
    rfl
  case true =>
    left
    rfl

example (b : Bool) : b = true ∨ b = false := by
  cases b
  · right; rfl
  · left; rfl

/-
  The with keyword changes how the cases tactic is parsed.
  Instead of executing and dumping the subgoals into the void,
  with acts as a syntactic gateway that opens a structured pattern-matching block.
-/
example (b : Bool) : b = true ∨ b = false := by
  cases b with
  | true => left; rfl
  | false => right; rfl

example (n : Nat) : n + 2 > 1 := by
  cases n
  · norm_num
  · norm_num

/-
  EXERCISE
-/
example (n : Nat) : n = 0 ∨ ∃ k, n = k + 1 := by
  cases n with
  | zero => left; rfl
  | succ k => right; use k;

/-
  An example using disjunction with three cases
-/
example (n : ℕ) (h : n = 1 ∨ n = 2 ∨ n = 3) : n ≤ 3 := by
  cases h
  case inl h1 =>   -- Case: n = 1
    rw [h1]; simp
  case inr h2 =>
    cases h2
    case inl h2 => -- Case: n = 2
      rw [h2]; simp
    case inr h3 => -- Case: n = 3
      rw [h3]


/-
  # RCASES

  If you want to recursively deconstruct all involved inductive types
  you can use `rcases`
-/
example (n : ℕ) (h : n = 1 ∨ n = 2 ∨ n = 3) : n ≤ 3 := by
  rcases h with ( h1 | h2 | h3)
  · rw [h1]; simp
  · rw [h2]; simp
  · rw [h3];

/-
  The `obtain` tactic that we used before uses `rcases`
-/
example (n : ℕ) (h : n = 1 ∨ n = 2 ∨ n = 3) : n ≤ 3 := by
  obtain  h1 | h2 | h3  := h
  · omega
  · omega
  · omega

/-
  Instead of repeating the same tactic for the different goals,
  we may use `all_goals`, or `repeat`, or the combinator `<;>`
-/
example (n : ℕ) (h : n = 1 ∨ n = 2 ∨ n = 3) : n ≤ 3 := by
  rcases h
  all_goals omega

example (n : ℕ) (h : n = 1 ∨ n = 2 ∨ n = 3) : n ≤ 3 := by
  rcases h
  repeat omega

example (n : ℕ) (h : n = 1 ∨ n = 2 ∨ n = 3) : n ≤ 3 := by
  rcases h <;> omega


/- EXERCISE
-/
example : ¬ (∃ n : ℕ, 17 * n = 2) := by
  push Not
  intro n
  have h:= Nat.eq_zero_or_pos n
  rcases h with (h | h)
  · rw [h]
    linarith
  · linarith


/-
  # FIN_CASES

  The `fin_cases` tactic is Lean's tool for brute-force enumeration.

  Use `cases` when you need to reason about the structure of a data type.

  Use `fin_cases` when the number of possible semantic values is small,
  and it is easier to just have Lean blindly check every single element.
-/

example : Fintype.card (Fin 5) = 5 := by simp

#check ({0, 2, 5} : Finset Nat)

def s : Finset Nat := {1,2,3}

example (n : ℕ) (h : n ∈ s) : n = 1 ∨ n = 2 ∨ n = 3 := by
  fin_cases h
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr rfl)

#check Finset

#check (Finset.range 5).image (fun x ↦ x * 2)



example (n : Fin 5) : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 := by
  fin_cases n
  all_goals simp


example (n : Fin 3) : n.val ^ 2 < 5 := by
  fin_cases n <;> norm_num


example (x : ℕ) (h : x ∈ [1, 2, 3]) : x < 4 := by
  fin_cases h <;> omega


inductive Color
  | red | green | blue
deriving Fintype

example (c : Color) : c = .red ∨ c = .green ∨ c = .blue := by
  fin_cases c
  -- Subgoal 1: c is replaced with Color.red
  · exact Or.inl rfl
  -- Subgoal 2: c is replaced with Color.green
  · exact Or.inr (Or.inl rfl)
  -- Subgoal 3: c is replaced with Color.blue
  · exact Or.inr (Or.inr rfl)

/-
  EXERCISE 3

  Replace the first sorry with the smallest possible value and
  Proove that the values of the polynomial on {0,1,2} are in that range.

  Hint: use `fin_cases`
-/
def fff := fun n => n^3 - n + 5
#eval fff 0
#eval fff 1
#eval fff 2
#eval Finset.range 3
example (n : ℕ) (h : n ∈ Finset.range 3) : n^3 - n + 5 ∈ Finset.range 12 := by
  fin_cases h <;> norm_num
