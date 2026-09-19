/-
Copyright (c) 2026 Iulian Simion. All rights reserved.
Released under the 3-Clause BSD License as described in the file LICENSE.
Authors: Iulian Simion, assisted by Claude (Anthropic) and Gemini (Google)
-/
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Data.Nat.Log

/-!
# Asymptotic growth

The **running time** of an algorithm on an input is the number of basic steps
that it performs, for a chosen notion of basic step. It is studied as a
function `T n` of the size `n` of the input, and it is compared with simple
functions such as `n`, `n ^ 2` or `log n`. The comparison ignores constant
factors, which depend on the notion of step, and it ignores the values of `T n`
for small `n`.

This comparison is expressed by **big-O notation**. For functions
`f g : ℕ → ℝ`, the function `f` is in `O(g)` when there are a constant `C` and a
threshold `N` such that `|f n| ≤ C * |g n|` for every natural number `n ≥ N`.

## Big-O in Mathlib

Mathlib writes `f =O[l] g`, where `l` is a **filter**, a collection of sets.
The notation `∀ᶠ n in l, P n` is a weaker form of `∀ n, P n`. The proposition
`∀ n, P n` states that the set `{n | P n}` of all numbers `n` with `P n` is the
whole of `ℕ`. The proposition `∀ᶠ n in l, P n` requires only that this set
belongs to `l`: the filter specifies which sets count as containing almost all
numbers. In this file, `f g : ℕ → ℝ` and `l` is the filter `atTop` on `ℕ`,
whose sets are those that contain all numbers from some `N` on. The proposition
`∀ᶠ n in atTop, P n` therefore states that `P n` holds for all sufficiently
large `n`, and the lemma `Filter.eventually_atTop` rewrites it to
`∃ N, ∀ n ≥ N, P n`.

The proposition `f =O[atTop] g` is equivalent to
`∃ C, ∀ᶠ n in atTop, ‖f n‖ ≤ C * ‖g n‖`, by the library lemma `isBigO_iff`.
Mathlib declares `IsBigO` irreducible, so Lean does not unfold `f =O[atTop] g`
to this form; the proofs below use lemmas such as `IsBigO.of_bound` instead. On
`ℝ`, the norm `‖x‖` is the absolute value `|x|`. With
`Filter.eventually_atTop`, the proposition becomes
`∃ C, ∃ N, ∀ n ≥ N, |f n| ≤ C * |g n|`, which is the definition of `f ∈ O(g)`
at the beginning of this file.

The values `T n` of a running time are natural numbers, the numbers of steps.
The functions compared below have values in `ℝ`, so a natural number `n`
appears in them as the real number `(n : ℝ)`.

Below, the set `O(g)` is defined from the relation `=O[atTop]` of Mathlib, so
that `f =O[atTop] g` can be written `f ∈ O(g)`. Textbooks also define `O(g)` as
a set; some of them write `f ∈ O(g)` for the membership, and others write
`f = O(g)`.
-/

open Asymptotics Filter

/-- The set of functions that grow at most as fast as `g`, up to a constant factor. -/
abbrev BigO (g : ℕ → ℝ) : Set (ℕ → ℝ) := {f | f =O[atTop] g}

notation "O(" g ")" => BigO g

/-!
The command `abbrev` makes a definition like `def`, and marks it as
**reducible**: automatic tactics such as `simp` unfold `BigO`, which they would
not do for a definition made with `def`. The command `notation` introduces new
syntax: Lean reads `O(g)` as `BigO g`, and displays `BigO g` as `O(g)`.
-/

example (f g : ℕ → ℝ) (h : f =O[atTop] g) : f ∈ O(g) := h
example (f g : ℕ → ℝ) (h : f ∈ O(g)) : f =O[atTop] g := h

/-!
The relation is transitive: `IsBigO.trans` derives `f ∈ O(h)` from `f ∈ O(g)`
and `g ∈ O(h)`.
-/

example {f g h : ℕ → ℝ} (h1 : f ∈ O(g)) (h2 : g ∈ O(h)) : f ∈ O(h) :=
  h1.trans h2

/-!
## Growth rates

The following functions serve as the points of comparison. The function
`Real.log` is the natural logarithm. Logarithms to different bases differ by a
constant factor, since `log₂ n = ln n / ln 2`, so the base does not matter
inside `O(·)`. Mathlib defines `Real.log 0 = 0` by convention.
-/

namespace Growth

/-- Constant growth: `n ↦ 1`. -/
def const : ℕ → ℝ := 1

/-- Linear growth: `n ↦ n`. -/
def linear : ℕ → ℝ := Nat.cast

/-- Quadratic growth: `n ↦ n ^ 2`. -/
def quadratic : ℕ → ℝ := fun n => (n : ℝ) ^ 2

/-- Logarithmic growth: `n ↦ ln n`. -/
noncomputable def logarithmic : ℕ → ℝ := fun n => Real.log (n : ℝ)

/-- Exponential growth: `n ↦ 2 ^ n`. -/
def exponential : ℕ → ℝ := fun n => (2 : ℝ) ^ n

end Growth

open Growth

namespace BigOExamples

/-!
## Bounds from known bounds

The examples in this section use only three library lemmas.
-/

example : linear ∈ O(linear) :=
  isBigO_refl linear atTop

/-!
The term `isBigO_refl u atTop` proves `u ∈ O(u)`.
-/

def f : ℕ → ℝ := fun n => 3 * n

example : f ∈ O(linear) := by
  have h_lin := isBigO_refl linear atTop
  exact h_lin.const_mul_left 3

/-!
For `h : u ∈ O(v)` and a constant `c`, the term `h.const_mul_left c` proves
`(fun n => c * u n) ∈ O(v)`. In the example, it proves that `n ↦ 3 * linear n`
is in `O(linear)`, and Lean identifies this function with `f` by unfolding
`linear`.
-/

def g : ℕ → ℝ := fun n => 5 * n + 2 * n

example : g ∈ O(linear) := by
  have h_lin := isBigO_refl linear atTop
  have h_left : (fun n => 5 * linear n) ∈ O(linear) := h_lin.const_mul_left 5
  have h_right : (fun n => 2 * linear n) ∈ O(linear) := h_lin.const_mul_left 2
  exact h_left.add h_right

/-!
For `h₁ : u₁ ∈ O(v)` and `h₂ : u₂ ∈ O(v)`, the term `h₁.add h₂` proves
`(fun n => u₁ n + u₂ n) ∈ O(v)`. In the example, it combines the bounds for
`n ↦ 5 * n` and `n ↦ 2 * n` into the bound for `g`.
-/

/-!
## Explicit constants and thresholds

The proofs above combine known bounds and never give the constant `C` or the
threshold `N` of the definition of `O(g)`; the numbers `3`, `5` and `2` in them
are coefficients of the functions. When a function is not built from functions
with known bounds, a proof provides `C` and `N` itself. The lemma `IsBigO.of_bound C`
reduces `f ∈ O(g)` to `∀ᶠ n in atTop, ‖f n‖ ≤ C * ‖g n‖`.

If the inequality holds for every `n`, the lemma `Eventually.of_forall` turns
it into the statement for all sufficiently large `n`. The first two lines of the
proof below display the goal `f ∈ O(g)` in the form `f =O[atTop] g`; the proof
also works without them, since `BigO` is reducible.
-/

def myBound (f g : ℕ → ℝ) : Prop := ∀ n, ‖f n‖ ≤ 5 * ‖g n‖

example {f g : ℕ → ℝ} (h : myBound f g) : f ∈ O(g) := by
  simp only [BigO]
  simp only [Set.mem_setOf_eq]
  apply IsBigO.of_bound 5
  exact Eventually.of_forall h

/-!
A threshold is needed when `g n = 0` and `f n ≠ 0` for some `n`, since no
constant `C` satisfies `‖f n‖ ≤ C * 0` there. The function `n ↦ 2 * n + 1` and
`linear` are an example, at `n = 0`.
-/

example : (fun n : ℕ => 2 * (n : ℝ) + 1) ∈ O(linear) := by
  apply IsBigO.of_bound 3
  rw [Filter.eventually_atTop]
  use 1
  intro n hn
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  simp only [linear, Real.norm_eq_abs]
  rw [abs_of_nonneg (by positivity), abs_of_nonneg (by positivity)]
  linarith

/-!
After `rw [Filter.eventually_atTop]`, the tactic `use 1` sets the threshold to
`1`, and `intro n hn` provides `hn : 1 ≤ n`, an inequality of natural numbers.
The goal `(1 : ℝ) ≤ n` of `hn'` is an inequality of real numbers, so
`exact hn` fails. The tactic `exact_mod_cast hn` stands for
`exact mod_cast hn`, "exact modulo casts": `mod_cast` rewrites the conversions
from `ℕ` to `ℝ` in the goal and in `hn` into a normal form, which turns the goal
into `1 ≤ n` on `ℕ`, and `exact` then closes it with `hn`. The lemma
`abs_of_nonneg` removes the absolute values of nonnegative numbers.

A larger threshold can replace a larger constant. The function `delayedLinear`
equals `n ^ 3` below `100` and `n` from `100` on. With the threshold `100`,
the constant `1` suffices.
-/

def delayedLinear (n : ℕ) : ℝ :=
  if n < 100 then
    (n : ℝ) ^ 3
  else
    (n : ℝ)

example : delayedLinear ∈ O(linear) := by
  apply IsBigO.of_bound 1
  rw [Filter.eventually_atTop]
  use 100
  intro n hn
  have h_not : ¬(n < 100) := by omega
  simp only [delayedLinear, linear, if_neg h_not, one_mul, le_refl]

end BigOExamples

/-!
## Comparing growth rates

Every function in `O(n)` is in `O(n ^ 2)`, by transitivity and the following
bound.
-/

theorem Growth.linear_isBigO_quadratic : linear ∈ O(quadratic) := by
  apply IsBigO.of_bound 1
  rw [Filter.eventually_atTop]
  use 1
  intro n hn
  simp only [linear, quadratic, one_mul, Real.norm_eq_abs]
  rw [abs_of_pos (by positivity), abs_of_pos (by positivity)]
  have hn_real : (1 : ℝ) ≤ n := by exact_mod_cast hn
  nlinarith

/-!
A polynomial is in the class of its term of highest degree. The linear term
`2 * n` of `3 * n ^ 2 + 2 * n` is bounded through `linear_isBigO_quadratic`.
-/

namespace BigOExamples

def f₂ : ℕ → ℝ := fun n => 3 * n ^ 2 + 2 * n

example : f₂ ∈ O(quadratic) := by
  have h_quad : (fun n => 3 * quadratic n) ∈ O(quadratic) :=
    (isBigO_refl quadratic atTop).const_mul_left 3
  have h_lin : (fun n => 2 * linear n) ∈ O(quadratic) :=
    ((isBigO_refl linear atTop).const_mul_left 2).trans linear_isBigO_quadratic
  exact h_quad.add h_lin

/-!
The logarithm to base `2` is a constant multiple of the natural logarithm, so
it is in `O(log n)`. The tactic `ext n` proves an equation of functions by
proving it at every `n`.
-/

noncomputable def g₂ : ℕ → ℝ := fun n => Real.log (n : ℝ) / Real.log 2

example : g₂ ∈ O(logarithmic) := by
  have h_eq : g₂ = fun n => (1 / Real.log 2) * logarithmic n := by
    ext n
    simp only [g₂, logarithmic]
    ring
  rw [h_eq]
  have h_log := isBigO_refl logarithmic atTop
  exact h_log.const_mul_left (1 / Real.log 2)

/-!
A shift of the exponent is a constant factor: `2 ^ (n + 3) = 2 ^ 3 * 2 ^ n`.
-/

example : (fun n => (2 : ℝ) ^ (n + 3)) ∈ O(exponential) := by
  have h_eq : (fun n => (2 : ℝ) ^ (n + 3)) = (fun n => 2 ^ 3 * exponential n) := by
    ext n
    simp only [exponential]
    rw [pow_add]
    ring
  rw [h_eq]
  have h_exp := isBigO_refl exponential atTop
  exact h_exp.const_mul_left ((2 : ℝ) ^ 3)

/-!
## Functions defined by recursion

The running time of a recursive algorithm is often given by a recursive
definition. A bound on it is proved by induction, and the bound is then
transferred to `O(·)`.

### Quadratic growth: a sum

The function `recSum` adds `n` at each step, so `recSum n` is
`0 + 1 + ⋯ + n = n * (n + 1) / 2`. The bound `recSum n ≤ n ^ 2` has a proof by
induction that needs no closed form.
-/

def recSum : ℕ → ℕ
  | 0 => 0
  | n + 1 => recSum n + (n + 1)

lemma recSum_bound (n : ℕ) : recSum n ≤ n ^ 2 := by
  induction n with
  | zero => decide
  | succ k ih =>
    unfold recSum
    calc
      recSum k + (k + 1) ≤ k ^ 2 + (k + 1) := Nat.add_le_add_right ih (k + 1)
      _ ≤ (k + 1) ^ 2 := by nlinarith

example : (fun n => (recSum n : ℝ)) ∈ O(quadratic) := by
  apply IsBigO.of_bound 1
  rw [Filter.eventually_atTop]
  use 0
  intro n _
  simp only [quadratic, one_mul]
  have h_pos1 : (0 : ℝ) ≤ recSum n := Nat.cast_nonneg _
  have h_pos2 : (0 : ℝ) ≤ (n : ℝ) ^ 2 := by positivity
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg h_pos1, abs_of_nonneg h_pos2]
  exact_mod_cast recSum_bound n

/-!
### Exponential growth: a closed form instead of a bound

The function `hanoi` satisfies `hanoi 0 = 1` and
`hanoi (n + 1) = 2 * hanoi n + 1`: `hanoi n` is the number of moves of the Tower
of Hanoi puzzle with `n + 1` disks.
The bound `hanoi n ≤ 2 ^ (n + 1)` is true, but a direct proof by induction
fails: from `hanoi k ≤ 2 ^ (k + 1)`, the step only gives
`hanoi (k + 1) ≤ 2 * 2 ^ (k + 1) + 1 = 2 ^ (k + 2) + 1`, which exceeds the
required bound by `1`.

A stronger statement goes through. The equation `hanoi n + 1 = 2 ^ (n + 1)` is
proved by induction: in the step, the induction hypothesis is now the equation
for `k`, which gives `hanoi (k + 1) + 1 = 2 * (hanoi k + 1) = 2 ^ (k + 2)`
exactly, with nothing left over. The bound follows from the equation. Proving a
stronger statement in order to obtain a stronger induction hypothesis is called
**strengthening the induction hypothesis**.
-/

def hanoi : ℕ → ℕ
  | 0 => 1
  | n + 1 => 2 * hanoi n + 1

lemma hanoi_closed_form (n : ℕ) : hanoi n + 1 = 2 ^ (n + 1) := by
  induction n with
  | zero => rfl
  | succ k ih =>
    unfold hanoi
    omega

lemma hanoi_upper_bound (n : ℕ) : hanoi n ≤ 2 * 2 ^ n := by
  have h : hanoi n + 1 = 2 * 2 ^ n := by
    calc hanoi n + 1 = 2 ^ (n + 1) := hanoi_closed_form n
      _ = 2 * 2 ^ n := by ring
  omega

example : (fun n => (hanoi n : ℝ)) ∈ O(exponential) := by
  apply IsBigO.of_bound 2
  rw [Filter.eventually_atTop]
  use 0
  intro n _
  simp only [exponential]
  have h_pos1 : (0 : ℝ) ≤ hanoi n := Nat.cast_nonneg _
  have h_pos2 : (0 : ℝ) ≤ (2 : ℝ) ^ n := by positivity
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg h_pos1, abs_of_nonneg h_pos2]
  exact_mod_cast hanoi_upper_bound n

end BigOExamples

/-!
### Logarithmic growth: halving

A recursion that halves its argument at each step performs about `log₂ n` steps.
The function `Nat.log2 n` is `⌊log₂ n⌋` for `n ≥ 1`, and `Nat.log2 0 = 0`. A
number `n ≥ 1` has `Nat.log2 n + 1` binary digits.

The bound `Nat.log2 n + 1 ∈ O(log n)` is proved with the constant `2 / ln 2`
and the threshold `2`. The two summands are bounded separately by
`ln n / ln 2`:

* `Nat.log2 n ≤ ln n / ln 2` for every `n`, by the library lemma
  `Real.log2_le_logb`; the function `Real.logb 2` is defined by
  `Real.logb 2 x = ln x / ln 2`;
* `1 ≤ ln n / ln 2` for `n ≥ 2`, since `ln 2 ≤ ln n` by `Real.log_le_log`.

The two inequalities add up to the bound.
-/

theorem Growth.log2_add_one_isBigO_logarithmic :
    (fun n : ℕ => (Nat.log2 n : ℝ) + 1) ∈ O(logarithmic) := by
  apply IsBigO.of_bound (2 / Real.log 2)
  rw [Filter.eventually_atTop]
  use 2
  intro n hn
  have h1 : (Nat.log2 n : ℝ) ≤ Real.log n / Real.log 2 := Real.log2_le_logb n
  have h2 : (1 : ℝ) ≤ Real.log n / Real.log 2 := by
    rw [le_div_iff₀ (Real.log_pos (by norm_num)), one_mul]
    exact Real.log_le_log (by norm_num) (by exact_mod_cast hn)
  simp only [logarithmic, Real.norm_eq_abs]
  rw [abs_of_nonneg (by positivity), abs_of_nonneg (Real.log_natCast_nonneg n)]
  calc (Nat.log2 n : ℝ) + 1
      ≤ Real.log n / Real.log 2 + Real.log n / Real.log 2 := add_le_add h1 h2
    _ = 2 / Real.log 2 * Real.log n := by ring

/-!
The function `halvings` halves its argument until it reaches `0`, and counts the
halvings: each call with `n ≠ 0` adds `1` for its own halving to the count of
the recursive call. It is defined by well-founded recursion, as `toBits` in `ToBits.lean`
of the first part: Lean proves automatically that `n / 2 < n` for `n ≠ 0`.

The function `Nat.log2` of Lean core satisfies
`Nat.log2 n = if 2 ≤ n then Nat.log2 (n / 2) + 1 else 0`, the library lemma
`Nat.log2_def`. Its recursion stops when `n < 2`, one step before the recursion
of `halvings`, and by strong induction, `halvings n = Nat.log2 n + 1` for
`n ≥ 1`.
-/

namespace BigOExamples

def halvings (n : ℕ) : ℕ :=
  if n = 0 then 0
  else halvings (n / 2) + 1

lemma halvings_eq (n : ℕ) (hn : 1 ≤ n) : halvings n = Nat.log2 n + 1 := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rw [halvings, if_neg (by omega)]
    by_cases h2 : 2 ≤ n
    · have h_log : Nat.log2 n = Nat.log2 (n / 2) + 1 := by
        rw [Nat.log2_def]
        simp [h2]
      rw [ih (n / 2) (by omega) (by omega), h_log]
    · have hn1 : n = 1 := by omega
      rw [hn1]
      simp [halvings, Nat.log2_def]

/-!
The functions `halvings` and `n ↦ Nat.log2 n + 1` agree for all `n ≥ 1`, so in
particular for all sufficiently large `n`. The bound of
`log2_add_one_isBigO_logarithmic` therefore carries over to `halvings`.
-/

example : (fun n => (halvings n : ℝ)) ∈ O(logarithmic) := by
  simp only [BigO]
  simp only [Set.mem_setOf_eq]
  refine log2_add_one_isBigO_logarithmic.congr' ?_ (EventuallyEq.refl _ _)
  rw [EventuallyEq, Filter.eventually_atTop]
  use 1
  intro n hn
  rw [halvings_eq n hn]
  push_cast
  ring

/-!
As in the proof with `myBound`, the two lines with `simp only` only display the
goal in the form `=O[atTop]`. The lemma `IsBigO.congr'` has three hypotheses,
`f₁ =O[l] g₁`, `f₁ =ᶠ[l] f₂` and `g₁ =ᶠ[l] g₂`, and it proves `f₂ =O[l] g₂`.
The notation `f₁ =ᶠ[l] f₂` stands for `∀ᶠ n in l, f₁ n = f₂ n`, by the
definition `EventuallyEq`.

The tactic `refine` applies a term in which some arguments are left open. Each
`?_` becomes a new goal. Each `_` must be filled in by Lean from the types, and
`refine` fails if it cannot be. In the proof above, the first hypothesis is
`log2_add_one_isBigO_logarithmic`. The second, `?_`, becomes the goal
`(fun n => (Nat.log2 n : ℝ) + 1) =ᶠ[atTop] fun n => (halvings n : ℝ)`, which
the remaining tactics prove. The third is `EventuallyEq.refl _ _`: the function
`logarithmic` eventually agrees with itself, and Lean fills in the two `_` with
`atTop` and `logarithmic`.

In the last steps, `push_cast` moves the conversion to `ℝ` into the sum,
turning `((Nat.log2 n + 1 : ℕ) : ℝ)` into `(Nat.log2 n : ℝ) + 1`, and `ring`
closes the resulting equation.
-/

/-!
## Exercises

Solutions: `solutions/TimeComplexity/Asymptotics.lean`.
-/

/-! ### 1
Prove that constant growth is in `O(n)`.

Hint: `linear 0 = 0`, so a threshold is needed. -/

theorem const_isBigO_linear : const ∈ O(linear) := sorry

/-! ### 2
Prove the bound below without providing a constant or a threshold, from
`isBigO_refl`, `const_mul_left`, `add`, `trans` and `linear_isBigO_quadratic`.
The function `fun n => (n : ℝ) ^ 2` is `quadratic` by definition. -/

theorem sq_add_isBigO_quadratic : (fun n : ℕ => (n : ℝ) ^ 2 + 4 * n) ∈ O(quadratic) :=
  sorry

/-! ### 3
The function `double` is defined by recursion. Prove that it is in `O(n)`.

Hint: prove `double n = 2 * n` by induction first. The equation of functions
`(fun n => (double n : ℝ)) = fun n => 2 * linear n` then follows with `ext n`
and `simp`. -/

def double : ℕ → ℕ
  | 0 => 0
  | n + 1 => double n + 2

theorem double_isBigO_linear : (fun n => (double n : ℝ)) ∈ O(linear) := sorry

end BigOExamples
