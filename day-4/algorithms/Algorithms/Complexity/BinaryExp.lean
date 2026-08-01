import Cslib.Algorithms.Lean.TimeM
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Log
import Algorithms.Complexity.Asymptotics
import Algorithms.Complexity.ToBits

open Cslib.Algorithms.Lean
open Asymptotics Filter
open ToBits

namespace FastExp

----------------------------------------------------------------------------------------------------
-- Fast exponentiation using TimeM
----------------------------------------------------------------------------------------------------


def fastExpTM (x : Nat) (bits : List Bool) : TimeM Nat Nat :=
  match bits with
  | [] => pure 1
  | b :: bs => do
    TimeM.tick 1
    let rest ← fastExpTM (x * x) bs
    if b then
      pure (x * rest)
    else
      pure rest


----------------------------------------------------------------------------------------------------
-- Closed form of the time function for fastExpTM
----------------------------------------------------------------------------------------------------

def fastExpTimeFunction (x : Nat) (N : Nat) : ℝ :=
  ((fastExpTM x (toBitsTM N).ret).time : ℝ)


----------------------------------------------------------------------------------------------------
-- Big-O formulation of the time complexity for fastExpTM
----------------------------------------------------------------------------------------------------


/-- The time cost of `fastExp` depends only on the length of the exponent's bit list. -/
theorem fastExp_time_eq_length (x : Nat) (bits : List Bool) :
    (fastExpTM x bits).time = bits.length := by
  induction bits generalizing x with
  | nil => rfl
  | cons b bs ih =>
    simp only [fastExpTM, TimeM.time_bind, TimeM.time_tick, ih, List.length_cons]
    split <;> simp [TimeM.time_pure] <;> omega

/-- The bit list produced by `toBitsTM n` has exactly as many entries as `toBitsTM n` ticks. -/
theorem toBitsTM_ret_length_eq_time (n : Nat) :
    (toBitsTM n).ret.length = (toBitsTM n).time := by
  unfold toBitsTM
  split
  · rfl
  · rename_i h_neq
    have ih := toBitsTM_ret_length_eq_time (n / 2)
    simp [ih]
    omega

/-- Proves that as N → ∞, the time complexity of fastExp is O(log_2 N). -/
theorem fastExp_time_isBigO_log2 (x : Nat) :
  fastExpTimeFunction x ∈ O(Growth.logarithmic)  := by
  have h_len : ∀ N : ℕ, (fastExpTM x (toBitsTM N).ret).time = (toBitsTM N).time := by
    intro N
    rw [fastExp_time_eq_length x (toBitsTM N).ret, toBitsTM_ret_length_eq_time N]
  have h_eq : ∀ᶠ N in atTop, toBitsTimeFunction N = fastExpTimeFunction x N := by
    filter_upwards [eventually_gt_atTop 0] with N hN
    unfold fastExpTimeFunction
    rw [h_len N]
    exact (toBitsTimeFunction_correct N hN).symm
  exact toBitsTimeFunction_isBigO_logarithmic.congr' h_eq (EventuallyEq.refl _ _)


end FastExp
