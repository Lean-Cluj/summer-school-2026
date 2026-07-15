import Mathlib.Algebra.Algebra.Defs
import Mathlib.Algebra.Module.BigOperators
import Mathlib.Algebra.Module.Pi
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.ZMod.Defs

open Finset Function
-------------------DEFINITIONS------------------------------------------
abbrev ℤ₂ (n : ℕ) := Fin n → ZMod 2

notation "ℤ₂^" n : max => ℤ₂ n

def e (i : Fin n) : ℤ₂^n := Pi.single i 1

def SF (f : ℤ₂^n → Fin n) : Prop :=
    ∀ (b : ℤ₂^n) (k : Fin n), ∃ (i : Fin n), f (b + e i) = k

def HasStrategy (n : ℕ) : Prop := ∃ f : ℤ₂^n → Fin n, SF f

def δ (i j : Fin n) : ℕ := if i = j then 1 else 0
--------------------FUNCTION SHIFT IS INJECTIVE--------------------------
lemma fun_shift_surj (f : ℤ₂^n → Fin n) (h : SF f) (b : ℤ₂^n) :
    Surjective (fun (i : Fin n) ↦ (f (b + e i) : Fin n)) := sorry

lemma fun_shift_inj (f : ℤ₂^n → Fin n) (h : SF f) (b : ℤ₂^n) :
    Injective (fun (i : Fin n) ↦ (f (b + e i) : Fin n)) := sorry
---------------------FUNCTION SHIFT SUM--------------------------------
lemma fun_shift_sum_one (f : ℤ₂^n → Fin n) (h : SF f) (b : ℤ₂^n) (k : Fin n) :
    ∑ i : Fin n, δ (f (b + e i)) k = 1 := sorry

lemma fun_shift_sum_pow2 (f : ℤ₂^n → Fin n) (h : SF f) (k : Fin n) :
    ∑ b, ∑ i, δ (f (b + e i)) k = 2 ^ n := sorry

lemma fun_shift_sum_rev (f : ℤ₂^n → Fin n) (h : SF f) (k i : Fin n) :
    ∑ b, δ (f (b + e i)) k = ∑ b, δ (f b) k := sorry
---------------------------MODUS PONENS-------------------------------
lemma strategy_pow2 (hn : 0 < n) (f : ℤ₂^n → Fin n) (h : SF f) :
    ∃ N, n * N = 2 ^ n := sorry

lemma mul_pow2 (h : ∃ N, n * N = 2 ^ n) : ∃ m, n = 2 ^ m := sorry

theorem puzzle_mp (hn : 0 < n) (h : HasStrategy n) : ∃ m, n = 2 ^ m := sorry
--------------------------MODUS PONENS REVERSE--------------------------
noncomputable def bij_Fin (m : ℕ) : Fin (2 ^ m) ≃ ℤ₂^m  := by
  apply Fintype.equivOfCardEq
  simp

lemma sum_basis (i : Fin n) (f : Fin n → ℤ₂^m) : ∑ j, e i j • f j = f i := sorry

theorem puzzle_mpr (hn : n = 2 ^ m) : HasStrategy n := sorry
------------------------------FINISH----------------------------------
theorem puzzle (hn : 0 < n) : HasStrategy n ↔ ∃ m, n = 2 ^ m := sorry
