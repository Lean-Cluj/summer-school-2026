/-
Copyright (c) 2026 Iulian Simion. All rights reserved.
Released under the 3-Clause BSD License as described in the file LICENSE.
Authors: Iulian Simion, assisted by Claude (Anthropic) and Gemini (Google)
-/
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.MinImports
import Mathlib.Tactic.Linter.Lint

/-!
# Maintenance utilities

This file covers three tools for maintaining a Lean library: the linters run by
`#lint`, which check declarations against the library's conventions;
`#min_imports`, which reports the imports a declaration needs; and `simp?`,
which reports a `simp only` call that can replace a `simp` call.

## Linters

A linter is an automatic check on declarations. It does not check correctness,
which the kernel does, but conventions for library code. The linter `simpNF`
checks lemmas tagged `@[simp]`.

The lemma below fails that check.
-/

section BadSimpLemma

@[local simp]
theorem bad_zero_add (x : ℕ) : 0 + x + 0 = x := by omega

/-!
Running

  `#lint only simpNF`

on it reports, among other lines:

```
#check bad_zero_add /- simp can prove this:
  by simp only [*, @zero_add, @add_zero]
One of the lemmas above could be a duplicate.
If that's not the case try reordering lemmas or adding @[priority]. -/
```

That is, the lemma is redundant: `simp` already reduces `0 + x + 0` to `x`
using `zero_add` and `add_zero`, so tagging this statement adds a rule that
can never fire on anything `simp` has not already simplified away.

The linter requires the left-hand side of a simp lemma to be in *simp-normal
form* — it must be something `simp` cannot
already rewrite. Otherwise `simp` normalises the term first and the rule
never matches.

The command is commented out below because `#lint` reports its findings as an
error, which would make the file fail to compile.
-/

-- #lint only simpNF

/-!
Stated without `@[simp]`, the same statement is an ordinary named theorem:
-/

theorem okay_zero_add (x : ℕ) : 0 + x + 0 = x := by simp

end BadSimpLemma

/-!
The command `#lint` with no arguments runs the whole suite — unused arguments,
missing docstrings, definitions that should be theorems, and so on — on the
*current file*. To lint more than that, there are forms such as `#lint in all`.
Mathlib's continuous integration runs the same suite of linters over the whole
library on every pull request, though it does so through `lake lint` rather
than through this command.

## `#min_imports`

Files accumulate imports. The command `#min_imports` reports the minimal set
of imports needed for a given command or term.

It takes the declaration as an argument; there is no form without one:

```
#min_imports in <command>
#min_imports in <term>
```
-/

#min_imports in
theorem plus_zero (x : ℕ) : x + 0 = x := rfl
--  reports: public import Mathlib.Data.Nat.Notation

/-!
## `simp?`

The tactic `simp` closes the goal but does not tell you how. Its variant
`simp?` does the same work and additionally reports the list of lemmas it used,
as a `simp only [...]` call you can paste back in.

The form `simp only [...]` is faster than `simp`, and its behaviour does not
change when a new `@[simp]` lemma is added to Mathlib.

There is a family of these: `exact?` searches the library for a lemma closing
the goal, `apply?` for one that applies to it, and `says` records the expected
output so that CI notices if it changes.
-/

example (x : ℕ) : x * 1 + 0 = x := by
  simp?
  -- reports: Try this: simp only [mul_one, add_zero]

-- the stable version of the same proof
example (x : ℕ) : x * 1 + 0 = x := by
  simp only [mul_one, add_zero]
