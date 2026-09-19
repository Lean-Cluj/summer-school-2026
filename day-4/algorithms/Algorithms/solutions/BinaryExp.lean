/-
Copyright (c) 2026 Iulian Simion. All rights reserved.
Released under the 3-Clause BSD License as described in the file LICENSE.
Authors: Iulian Simion, assisted by Claude (Anthropic) and Gemini (Google)
-/
import Mathlib.Tactic.Ring
import Algorithms.BinaryExp

/-! # Solutions — Exponentiation by squaring -/

namespace FastExp.Solutions

-- 1
theorem powNaive_eq (x n : Nat) : powNaive x n = x ^ n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change powNaive x n * x = x ^ (n + 1)
    rw [ih, pow_succ]

-- 2
theorem fastExp_one (bits : List Bool) : fastExp 1 bits = 1 := by
  induction bits with
  | nil => rfl
  | cons b bs ih =>
    cases b with
    | true =>
      change 1 * fastExp (1 * 1) bs = 1
      rw [Nat.mul_one, ih]
    | false =>
      change fastExp (1 * 1) bs = 1
      rw [Nat.mul_one, ih]

-- 3
theorem fastExp_mul (x y : Nat) (bits : List Bool) :
    fastExp (x * y) bits = fastExp x bits * fastExp y bits := by
  induction bits generalizing x y with
  | nil => rfl
  | cons b bs ih =>
    have hsq : x * y * (x * y) = x * x * (y * y) := by ring
    cases b with
    | true =>
      change x * y * fastExp (x * y * (x * y)) bs
        = (x * fastExp (x * x) bs) * (y * fastExp (y * y) bs)
      rw [hsq, ih (x * x) (y * y)]
      ring
    | false =>
      change fastExp (x * y * (x * y)) bs = fastExp (x * x) bs * fastExp (y * y) bs
      rw [hsq, ih (x * x) (y * y)]

end FastExp.Solutions
