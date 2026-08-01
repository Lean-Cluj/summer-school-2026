import Cslib.Algorithms.Lean.TimeM
import Mathlib.Data.Tree.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Algorithms.Complexity.Asymptotics

open Cslib.Algorithms.Lean
open Asymptotics Filter


namespace BinaryTree


----------------------------------------------------------------------------------------------------
-- Check that an elment is present in a Binary Search Tree (BST)
----------------------------------------------------------------------------------------------------


#check BinaryTree.height

def bstSearchTM (t : BinaryTree Nat) (target : Nat) : TimeM Nat Bool :=
  match t with
  | .nil => pure false
  | .node v l r => do
    TimeM.tick 1
    if target == v then
      pure true
    else if target < v then
      bstSearchTM l target
    else
      bstSearchTM r target


----------------------------------------------------------------------------------------------------
-- Upper bound for the time function for bstSearchTM
----------------------------------------------------------------------------------------------------

noncomputable def bstSearchTimeFunctionBound (n : ℕ) : ℝ := Real.log (n + 1) / Real.log 2


-- in O(log N) time, where N is the number of nodes in the tree.

theorem bstSearchTimeFunctionBound_aux (t : BinaryTree Nat) (target : Nat) :
  (bstSearchTM t target).time ≤ t.height := by
  induction t with
  | nil =>
    change 0 ≤ 0
    omega
  | node v l r ih_l ih_r =>
    have step : (bstSearchTM (BinaryTree.node v l r) target).time =
      1 + (if target == v then pure true
           else if target < v then bstSearchTM l target
           else bstSearchTM r target).time := by rfl
    rw [step]
    have h : (BinaryTree.node v l r).height = max l.height r.height + 1 := by rfl
    rw [h]
    split
    · change 1 + 0 ≤ max l.height r.height + 1
      omega
    · split
      · omega
      · omega


/-- A BST is *dense* when it needs the fewest nodes possible to reach its height: no fewer than
`2 ^ height - 1` nodes, i.e. `2 ^ height ≤ numNodes + 1`. This is the exact structural property
that lets search run in `O(log N)` time (e.g. a complete/balanced BST is dense); an arbitrary,
unbalanced BST is not, and its search time is only bounded by its height, which can be as large
as its node count. -/
theorem bstSearchTimeFunctionBound_correct {t : BinaryTree Nat} (target : Nat)
    (hd : 2 ^ t.height ≤ t.numNodes + 1) :
    ((bstSearchTM t target).time : ℝ) ≤ bstSearchTimeFunctionBound t.numNodes := by
  have h_time_le_height : (bstSearchTM t target).time ≤ t.height :=
    bstSearchTimeFunctionBound_aux t target
  have h_pow_real : (2 : ℝ) ^ t.height ≤ ((t.numNodes + 1 : ℕ) : ℝ) := by exact_mod_cast hd
  have h_log_le := Real.log_le_log (by positivity) h_pow_real
  rw [Real.log_pow] at h_log_le
  have h_log2_pos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have h_height_le : (t.height : ℝ) ≤ Real.log ((t.numNodes : ℝ) + 1) / Real.log 2 := by
    rw [le_div_iff₀ h_log2_pos]
    push_cast at h_log_le
    linarith
  calc ((bstSearchTM t target).time : ℝ)
      ≤ (t.height : ℝ) := by exact_mod_cast h_time_le_height
    _ ≤ Real.log ((t.numNodes : ℝ) + 1) / Real.log 2 := h_height_le
    _ = bstSearchTimeFunctionBound t.numNodes := rfl


----------------------------------------------------------------------------------------------------
-- Big-O formulation of the time complexity for bstSearchTM
----------------------------------------------------------------------------------------------------


theorem bstSearchTimeFunctionBound_isBigO_logarithmic :
  bstSearchTimeFunctionBound ∈ O(Growth.logarithmic) := by
  refine IsBigO.of_bound (2 / Real.log 2) ?_
  filter_upwards [eventually_ge_atTop 2] with n hn
  have hn2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have h_log_mono := Real.log_le_log (by norm_num) hn2
  have h_log2_pos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  -- We need to prove `‖bstSearchTimeFunction n‖ ≤ (2 / Real.log 2) * ‖Growth.logarithmic n‖`
  simp only [bstSearchTimeFunctionBound, Growth.logarithmic, Real.norm_eq_abs]
  have h_log_np1_nonneg : (0 : ℝ) ≤ Real.log ((n : ℝ) + 1) := by
    apply Real.log_nonneg
    linarith
  have h_pos : (0 : ℝ) ≤ Real.log ((n : ℝ) + 1) / Real.log 2 := by positivity
  rw [abs_of_nonneg h_pos]
  have h_log_pos : (0 : ℝ) ≤ Real.log (n : ℝ) := h_log_mono.trans' (Real.log_pos (by norm_num)).le
  rw [abs_of_nonneg h_log_pos]
  -- `n + 1 ≤ 2 * n` for `n ≥ 2`, so `log (n + 1) ≤ log 2 + log n`
  have h_np1_le : (n : ℝ) + 1 ≤ 2 * (n : ℝ) := by linarith
  have h_log_np1_le : Real.log ((n : ℝ) + 1) ≤ Real.log (2 * (n : ℝ)) :=
    Real.log_le_log (by linarith) h_np1_le
  have h_log_2n : Real.log (2 * (n : ℝ)) = Real.log 2 + Real.log (n : ℝ) :=
    Real.log_mul (by norm_num) (by positivity)
  rw [h_log_2n] at h_log_np1_le
  -- Divide by `Real.log 2` and absorb the constant `1` into `log n / log 2 ≥ 1`
  have h_one_le : (1 : ℝ) ≤ Real.log (n : ℝ) / Real.log 2 := by
    rw [le_div_iff₀ h_log2_pos, one_mul]
    exact h_log_mono
  rw [div_le_iff₀ h_log2_pos]
  calc Real.log ((n : ℝ) + 1) ≤ Real.log 2 + Real.log (n : ℝ) := h_log_np1_le
    _ ≤ Real.log (n : ℝ) / Real.log 2 * Real.log 2 + Real.log (n : ℝ) := by
        have := mul_le_mul_of_nonneg_right h_one_le h_log2_pos.le
        rw [one_mul] at this
        linarith
    _ = 2 / Real.log 2 * Real.log (n : ℝ) * Real.log 2 := by field_simp; ring



end BinaryTree
