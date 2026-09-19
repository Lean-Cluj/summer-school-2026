import Mathlib.Algebra.Module.BigOperators
import Mathlib.Algebra.Module.Pi
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.ZMod.Defs

-------------------DEFINITIONS------------------------------------------
abbrev Z2 (n : ℕ) := Fin n → ZMod 2
notation "ℤ₂^" n : max => Z2 n

def e (i : Fin n) : ℤ₂^n := Pi.single i 1

def SF (f : ℤ₂^n → Fin n) : Prop :=
    ∀ (b : ℤ₂^n) (k : Fin n), ∃ (i : Fin n), f (b + e i) = k

def HasStrategy (n : ℕ) : Prop := ∃ f : ℤ₂^n → Fin n, SF f

def δ (i j : Fin n) : ℕ := if i = j then 1 else 0
--------------------FUNCTION SHIFT IS INJECTIVE--------------------------
lemma fun_shift_surj : True := sorry

lemma fun_shift_inj : True := sorry
---------------------FUNCTION SHIFT SUM--------------------------------
lemma fun_shift_sum_one : True := sorry

lemma fun_shift_sum_pow2 : True := sorry

lemma fun_shift_sum_rev : True := sorry
---------------------------MODUS PONENS-------------------------------
lemma strategy_pow2 : True := sorry

lemma mul_pow2 : True := sorry

theorem puzzle_mp : True := sorry
--------------------------MODUS PONENS REVERSE--------------------------
noncomputable def bij_Fin : True := sorry

lemma sum_basis : True := sorry

theorem puzzle_mpr : True := sorry
------------------------------FINISH----------------------------------
theorem puzzle : True := sorry
