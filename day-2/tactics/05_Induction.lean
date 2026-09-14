/-
Copyright (c) 2026 Iulian Simion. All rights reserved.
Released under the 3-Clause BSD License as described in the file LICENSE.
Authors: Iulian Simion, assisted by Claude (Anthropic) and Gemini (Google)
-/
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.GCongr
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Algebra.Order.Ring.Pow

/-!
# Induction

The tactic `cases n` uses that every natural number is either `0` or `k + 1`.
Simple induction uses the same split, and adds one thing: in the `k + 1` branch
you may assume the statement for `k`.

In Lean, this is the tactic `induction`, and the extra assumption appears in
the context under whatever name you give it — `ih`, for induction hypothesis,
by convention.

The syntax mirrors `cases`:

```
induction n with
| zero => …
| succ k ih => …
```

## Example 1: `2 ^ n ≥ n + 1`

The base case is `2 ^ 0 ≥ 0 + 1`, i.e. `1 ≥ 1`. In the step, we know
`ih : 2 ^ k ≥ k + 1` and must prove `2 ^ (k + 1) ≥ k + 2`.

The `calc` chain is the paper proof, line for line. The step `rel [ih]` is the
one that uses the induction hypothesis: it replaces `2 ^ k` by the smaller
`k + 1` inside `2 * 2 ^ k`, which is legitimate because multiplying both sides
of `ih` by `2` gives `2 * 2 ^ k ≥ 2 * (k + 1)`.
-/

example (n : ℕ) : 2 ^ n ≥ n + 1 :=
  by
    induction n with
    | zero => norm_num
    | succ k ih =>
      calc 2 ^ (k + 1)
          = 2 * 2 ^ k := by ring
        _ ≥ 2 * (k + 1) := by rel [ih]
        _ = (k + 1 + 1) + k := by ring
        _ ≥ k + 1 + 1 := by norm_num

-- the same statement, leaving the step to automation
example (n : ℕ) : 2 ^ n ≥ n + 1 :=
  by
    induction n with
    | zero => norm_num
    | succ k ih => omega

/-!
## Example 2: a positive rational stays positive

Here, the induction hypothesis is not handed to `rel`, as in Example 1. It is
passed directly as an argument to a lemma — `mul_pos hq ih` — which then
justifies the first step of the `calc`.
-/

theorem rat_pow_pos (q : ℚ) (hq : 0 < q) (k : ℕ) : 0 < q ^ k :=
  by
    induction k with
    | zero => simp
    | succ k ih =>
      calc (0 : ℚ)
          < q * q ^ k := mul_pos hq ih
        _ = q ^ (k + 1) := by ring

-- the tactic `positivity` proves the same statement directly
theorem rat_pow_pos' (q : ℚ) (hq : 0 < q) (k : ℕ) : 0 < q ^ k := by positivity

/-!
## Example 3: Bernoulli's inequality

For `a ≥ -1`, `(1 + a) ^ n ≥ 1 + n * a`.

Since `n` is a natural number and the inequality is in `ℝ`, `n` is coerced;
`push_cast` normalises the coercions, and `(k : ℝ)` denotes the coerced value.
The last step is non-linear, since it needs `k * a ^ 2 ≥ 0`, so it uses
`nlinarith` rather than `linarith`.
-/

theorem bernoulli_inequality (a : ℝ) (ha : -1 ≤ a) (n : ℕ) :
    (1 + a) ^ n ≥ 1 + n * a :=
  by
    induction n with
    | zero =>
      norm_num
    | succ k ih =>
      push_cast
      have ha2 : 1 + a ≥ 0 := by linarith
      have hk : (k : ℝ) ≥ 0 := Nat.cast_nonneg k
      calc (1 + a) ^ (k + 1)
          = (1 + a) * (1 + a) ^ k := by ring
        _ ≥ (1 + a) * (1 + k * a) := by rel [ih]
        _ = k * a ^ 2 + (1 + (k + 1) * a) := by ring
        _ ≥ 1 + (k + 1) * a := by nlinarith

/-!
Mathlib's version, `one_add_mul_le_pow`, needs only `-2 ≤ a` and holds in any
linearly ordered ring, so the theorem above is a special case of it.
-/

example (a : ℝ) (ha : -1 ≤ a) (n : ℕ) : (1 + a) ^ n ≥ 1 + n * a :=
  one_add_mul_le_pow (by linarith) n

/-!
# Recursion and induction

A function on `ℕ` may be defined by two equations, giving its value at `0` and
its value at `n + 1` in terms of its value at `n`. These equations *are* the
definition, which is why `rfl` and `show` can use them directly, and `rw` and
`simp` can use them when given the name, as in `rw [sumTo]`.
-/

def sumTo : ℕ → ℕ
  | 0 => 0
  | n + 1 => (n + 1) + sumTo n

#eval sumTo 4   -- 0 + 1 + 2 + 3 + 4

/-!
Proofs about such a function go by induction, and the step case is where the
defining equation gets used. The tactic `show` restates the goal in a
definitionally equal form, here the unfolded one.
-/

example (n : ℕ) : 2 * sumTo n = n * (n + 1) :=
  by
    induction n with
    | zero => rfl
    | succ k ih =>
      -- the term `sumTo (k + 1)` unfolds to `(k + 1) + sumTo k`
      show 2 * ((k + 1) + sumTo k) = (k + 1) * (k + 2)
      calc 2 * ((k + 1) + sumTo k)
          = 2 * (k + 1) + 2 * sumTo k := by ring
        _ = 2 * (k + 1) + k * (k + 1) := by rw [ih]
        _ = (k + 1) * (k + 2) := by ring

/-!
# Two-step induction

Some definitions look back further than one step. The function below is defined
by recursion as `sumTo` was, but each value is built from the *two* before it,
so it needs two base cases.
-/

def u : ℕ → ℕ
  | 0 => 1
  | 1 => 3
  | n + 2 => u (n + 1) + 6 * u n

#eval [u 0, u 1, u 2, u 3, u 4, u 5]

/-!
The values printed are the powers of three, and that is what we prove.

Simple induction on this statement does not reach it. In the step case, you
would hold `ih : u k = 3 ^ k` with the goal `u (k + 1) = 3 ^ (k + 1)`, and the
defining equations say nothing about `u (k + 1)` until `k` is itself split into
`0` and `j + 1`. In the second of those, the value is `u (j + 1) + 6 * u j`, and
nothing is known about `u j`.

What the proof needs is the statement at the *two* preceding numbers, and
Mathlib packages exactly that as `Nat.twoStepInduction`: two base cases, and a
step with two hypotheses. A named rule is supplied to the tactic with
`induction … using`.
-/

#check @Nat.twoStepInduction

theorem u_eq (n : ℕ) : u n = 3 ^ n :=
  by
    induction n using Nat.twoStepInduction with
    | zero => rfl
    | one => rfl
    | more k ihk ihk1 =>
      -- ihk : u k = 3 ^ k,   ihk1 : u (k + 1) = 3 ^ (k + 1)
      show u (k + 1) + 6 * u k = 3 ^ (k + 2)
      rw [ihk, ihk1]
      ring

/-!
The recurrence reaches back a fixed distance, two, so two hypotheses suffice,
and the rule supplies exactly two. A recurrence of depth three needs three base
cases and three hypotheses, and so on.

# Strong induction

Simple induction proves the statement at `k + 1` from the statement at `k`,
and two-step induction proves it at `k + 2` from those at `k` and `k + 1`: in
both, the numbers used lie a fixed distance below. Strong induction is for
proofs where that distance is *not* fixed, such as proofs that use a divisor of
`n`, which may lie anywhere below `n`. It gives the statement for every smaller
number at once, so the hypothesis has the shape

  `ih : ∀ m, m < n → P m`

which is a function: to use it at a particular `m` you supply `m` together with
a proof that `m < n`.

Take the fact that every `n ≥ 2` has a prime factor. If `n` is prime, it is its
own prime factor. If not, it has a divisor `m` with `2 ≤ m < n`, and any prime
factor of `m` is also one of `n`. No fixed number of hypotheses would do here,
since nothing says how far below `n` that divisor sits.
-/

#check @Nat.strong_induction_on
#check @Nat.exists_dvd_of_not_prime2

theorem exists_prime_factor (n : ℕ) (hn : 2 ≤ n) : ∃ p, p.Prime ∧ p ∣ n :=
  by
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      by_cases hp : n.Prime
      · -- the number `n` is prime, so it is its own prime factor
        exact ⟨n, hp, dvd_refl n⟩
      · -- otherwise `n` has a divisor `m` with `2 ≤ m` and `m < n`
        obtain ⟨m, hmn, hm2, hmlt⟩ := Nat.exists_dvd_of_not_prime2 hn hp
        obtain ⟨p, hp', hpm⟩ := ih m hmlt hm2
        exact ⟨p, hp', hpm.trans hmn⟩

/-!
The rule has a single case, named `h`; the `_` in `| _ n ih` stands for that
name, which the proof leaves unwritten.

The tactic `by_cases` splits on whether `n` is prime. In the second branch, the
first `obtain` names the three parts of what `Nat.exists_dvd_of_not_prime2`
gives: `hmn : m ∣ n`, `hm2 : 2 ≤ m` and `hmlt : m < n`. The hypothesis `ih` has
the type `∀ m < n, 2 ≤ m → ∃ p, p.Prime ∧ p ∣ m`, so `ih m hmlt hm2` is the
statement at `m`; the second `obtain` names its parts `hp' : p.Prime` and
`hpm : p ∣ m`, and `hpm.trans hmn` gives `p ∣ n`. The statement is available at
`m` because strong induction supplies every smaller case; two-step induction
would supply it only at `n - 1` and `n - 2`.

For statements holding from some point on, such as "for every `n ≥ 3`", Mathlib
provides `Nat.le_induction`, which gives the base case at the starting point.
-/

/-!
# Induction is not a fact about `ℕ`

Induction is available for *any* inductive type: it is case analysis on the
constructors, with an induction hypothesis added for each recursive argument.

The type `List` has two constructors, `nil` and `cons`, so induction on a list
has two cases, named after them.
-/

example {α : Type} (xs ys : List α) :
    (xs ++ ys).length = xs.length + ys.length :=
  by
    induction xs with
    | nil => simp
    | cons x xs ih => simp [ih]; omega

/-!
The case names are the constructors of `List`.
-/

/-!
# Exercises

Solutions: `solutions/05_Induction.lean`. Further exercises: section 5 of
`09_Exercises.lean`.
-/

/-! ## 1 — the sum of the first `n` odd numbers

The value `sumOdd n` is `1 + 3 + ⋯ + (2n − 1)`, defined by recursion. Prove
the closed formula. This is the same shape as the `sumTo` example above.

Hints: in the step, the goal mentions `sumOdd (k + 1)`, which unfolds to
`(2 * k + 1) + sumOdd k`. The tactic `show` lets you write the goal in that
unfolded form; from there, `rw [ih]` and `ring` finish the proof. -/

def sumOdd : ℕ → ℕ
  | 0 => 0
  | n + 1 => (2 * n + 1) + sumOdd n

#eval sumOdd 4   -- 1 + 3 + 5 + 7

theorem ex1 (n : ℕ) : sumOdd n = n ^ 2 := sorry

/-! ## 2 — two-step induction

The sequence `v` is built the way `u` was above: each value from
the two before it. Compute the first few with the `#eval` below, guess the
closed form, and prove it.

Hint: use `induction n using Nat.twoStepInduction`, whose cases are named
`zero`, `one` and `more`. The two base cases close by `rfl`; in `more` you are
given the statement at `k` and at `k + 1`. -/

def v : ℕ → ℕ
  | 0 => 2
  | 1 => 4
  | n + 2 => v (n + 1) + 2 * v n

#eval [v 0, v 1, v 2, v 3, v 4, v 5]

theorem ex2 (n : ℕ) : v n = 2 ^ (n + 1) := sorry

/-! ## 3 — strong induction

Every positive natural number is a power of two times an odd number. This one
needs strong induction rather than the two-step rule: for an even `n` the
argument appeals to `n / 2`, which is not a fixed distance below `n`.

Hints: `induction n using Nat.strong_induction_on`; split with
`rcases Nat.even_or_odd n with he | ho`. In Lean, `Even n` unfolds to
`∃ r, n = r + r`, so `obtain ⟨j, hj⟩ := he` gives `hj : n = j + j`; the facts
`0 < j` and `j < n` both follow by `omega`. The odd case needs no induction
hypothesis at all. -/

theorem ex3 (n : ℕ) (hn : 0 < n) : ∃ k m, Odd m ∧ n = 2 ^ k * m := sorry
