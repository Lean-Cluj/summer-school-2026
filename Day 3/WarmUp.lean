import Mathlib.Algebra.Algebra.Defs
import Mathlib.Algebra.Module.BigOperators
import Mathlib.Algebra.Module.Pi
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.ZMod.Defs

------------------------------------------
#check (5 : Fin 10).val
#check (5 : Fin 10).isLt

example (i : Fin 10) : i.val < 10 := sorry

#check (Fin.mk 0 (Nat.zero_lt_succ 9) : Fin 10)
#check (⟨0, by exact?⟩ : Fin 10)
#eval (⟨0, Nat.two_pos⟩ : Fin 2) = (⟨0, Nat.zero_lt_succ 1⟩ : Fin 2)
-- example why `proof irrelevance` is crucial

example (hn : 0 < n) : Fin n := sorry
-----------------------------------------------
#eval Fintype.card (Fin 10)

example : Fintype.card (Fin n) = n := by sorry

#eval ∑ (i : Fin 10), i

example : ∑ (i : Fin n), 1 = n := by sorry
-- rewrite using `Fintype.card_eq_sum_ones`
-----------------------------------------------
#check ({0,1,2,3,4} : Finset ℕ)
#eval ∑ (i ∈ {1,2,3,4}), i
#check ∑ (i ∈ {1,2,3,4}), i

#check ({0,1,2,3,4} : Finset (Fin 10))
#eval ∑ (i ∈ ({1,2,3,4} : Finset (Fin 10))), i
#check ∑ (i ∈ ({1,2,3,4} : Finset (Fin 10))), i

#check (Finset.univ : Finset (Fin 10))
#eval (Finset.univ : Finset (Fin 10)) = {0,1,2,3,4,5,6,7,8,9}
#eval Finset.card (Finset.univ : Finset (Fin 10))

example : Finset.card (Finset.univ : Finset (Fin n)) = n := by sorry

example (f : Fin n → ℕ) : ∑ (i ∈  Finset.univ), f i = ∑ (i : Fin n), f i := rfl

example : ∑ (i ∈  (Finset.univ : Finset (Fin n))), 1 = n := by sorry
-----------------------------------------------
abbrev Z2 (n : ℕ) := Fin n → ZMod 2
notation "ℤ₂^" n : max => Z2 n -- think about `ℤ₂^n` as `ℤ₂×ℤ₂×...×ℤ₂`

example (v₁ : ℤ₂^n) (v₂ : ℤ₂^n) : ℤ₂^n := v₁ + v₂
example (v : ℤ₂^n) (α : ZMod 2) : ℤ₂^n := α • v
-- is this working if we replace `ZMod 2` by `Fin 2`? why?
example : (ZMod 2) = (Fin 2) := rfl
------------------------------------------------
#synth (Module (ZMod 2) (ℤ₂^10))
-- #synth (Module (Fin 2) (ℤ₂^10)) -- fails to synthetize
-- #synth Semiring (Fin 2)  -- fails to synthetize
#synth Semiring (ZMod 2)
----------------------------------------------------
def e (i : Fin n) : ℤ₂^n := Pi.single i 1

#eval List.ofFn (e (2 : Fin 6))
#eval List.ofFn (e (2 : Fin 6) + e 3 + e 5)
#eval List.ofFn (e (2 : Fin 6) + e 2 + e 5)

example (i₀ : Fin n) : ∑ i, e i i₀ = 1 := by sorry
-- hint : `rw [Fintype.sum_eq_single i₀]`
-----------------------------------------------
def δ (i j : Fin n) : ℕ := if i = j then 1 else 0

example (i₀ : Fin n) : ∑ i, δ i i₀ = 1 := by sorry
-----------------------------------------------
example : Function.Bijective (fun (i : ZMod n) ↦ i + 1) := by sorry
-----------------------------------------------
example (f : Fin n → Fin n) (hf : Function.Injective f) :
    Function.Surjective f := by sorry
example (f : Fin n → Fin n) (hf : Function.Surjective f) :
    Function.Injective f := by sorry
----------------------------------------------
example (h : α ≃ β) (x : α) : h.invFun (h.toFun x) = x := by sorry

example (f : α ≃ β) : f.symm ∘ f = id := by sorry

noncomputable example : ℤ₂^n ≃ Fin (2^n) := by sorry
-- apply `Fintype.equivOfCardEq` -- use `simp`
-----------------------------------------------
example (n N m : ℕ) (h : n * N = m) : n ∣ m := by sorry

example (h : n ∣ p ^ m) (hp : Nat.Prime p) : ∃ k, n = p ^ k := by
 sorry
-- use `Nat.dvd_prime_pow`
