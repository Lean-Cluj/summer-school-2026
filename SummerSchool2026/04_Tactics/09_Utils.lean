/-
Copyright (c) 2026 Iulian Simion. All rights reserved.
Released under the 3-Clause BSD License as described in the file LICENSE.txt.
Authors: Iulian Simion

Note: Parts of this file were synthesized with the assistance of Gemini 3.1 Pro.
-/
import Mathlib.Data.Real.Basic

/-
  # Linters
-/

-- BAD: The linter will flag this.
-- Why? `simp` automatically evaluates `0 + x` to `x` using `zero_add`.
-- So, it will change the left side to `x + 0` before it even tries to apply your lemma!
@[simp]
theorem bad_zero_add (x : ℕ) : 0 + x + 0 = x := by omega

-- GOOD: Either remove the `@[simp]` attribute if you just want it as a helper lemma,
-- or don't write it at all, because `simp` already solves `0 + x + 0 = x` natively.
lemma okay_zero_add (x : ℕ) : 0 + x + 0 = x := by simp

/-
  When you type #lint at the bottom of a Lean file,
  it triggers an automated metaprogram that scans the abstract syntax tree of your code.
-/

--#lint

/-
  To run a targeted check without firing off the entire suite,
  use the `only` keyword followed by the exact names of the linters you want to run.
-/

--#lint only simpNF

/-
  # Other useful utilities

  If you have imported too many files or are relying on a massive global import,
  you can place #minimize_imports at the very bottom of your Lean file.
-/

-- #min_imports


/-
  When you use simp?, Lean runs the simplifier normally,
  but it secretly tracks every single lemma it pulls
  from the global dictionary to close the goal.
-/
example (x : ℕ) : x * 1 + 0 = x := by
  simp?
