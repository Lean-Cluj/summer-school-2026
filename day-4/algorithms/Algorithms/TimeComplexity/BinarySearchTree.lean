/-
Copyright (c) 2026 Iulian Simion. All rights reserved.
Released under the 3-Clause BSD License as described in the file LICENSE.
Authors: Iulian Simion, assisted by Claude (Anthropic) and Gemini (Google)
-/
import Cslib.Algorithms.Lean.TimeM
import Mathlib.Data.Tree.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Algorithms.TimeComplexity.Asymptotics
import Algorithms.BinarySearchTree

open Cslib.Algorithms.Lean
open Asymptotics Filter

/-!
# Counting steps: search in a binary search tree

The function `bstSearchTM` is `bstSearch` from `BinarySearchTree.lean` of the
first part, with the result type `TimeM ℕ Bool` in place of `Bool` and with one
tick for each node visited. The search follows one path from the root, so its
cost is at most the **height** of the tree, the number of nodes on a longest
path from the root. Mathlib defines it as `BinaryTree.height`, with
`height nil = 0` and `height (node v l r) = max l.height r.height + 1`. This
height counts nodes; many textbooks count edges, so that their height is one
less. The number of nodes is `BinaryTree.numNodes`; Mathlib calls them internal
nodes, since it counts each `nil` as a leaf.

The height is not determined by the number of nodes. A tree in which every left
subtree is empty has height equal to its number of nodes `N`, and the search
may visit every node. The cost is in `O(log N)` only for families of trees in
which the height grows like the logarithm of the number of nodes.
-/

namespace BinaryTree

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

#eval (bstSearchTM myTree 7).time  -- 3

/-!
## The cost is at most the height

The proof is by induction on the tree. At a node, the cost is `1` plus the cost
of the search in one subtree, which is at most the height of that subtree by
the induction hypothesis, and hence at most `max l.height r.height`.
-/

theorem bstSearchTM_time_le_height (t : BinaryTree Nat) (target : Nat) :
    (bstSearchTM t target).time ≤ t.height := by
  induction t with
  | nil => rfl
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

/-!
## Perfect trees

A tree of height `h` has at most `2 ^ h - 1` nodes. The hypothesis
`2 ^ height ≤ numNodes + 1` below states that it has exactly that many: the
tree is **perfect**, that is, every node has two nonempty subtrees or two empty
ones, and all nodes with two empty subtrees have the same distance from the
root. The tree `myTree`, defined in `BinarySearchTree.lean` of the first part,
is perfect, with height `3` and `7` nodes. For a perfect tree with `N` nodes,
`height ≤ log₂ (N + 1)`, and the cost of the search is at most
`log (N + 1) / log 2`, the function `bstSearchTimeFunctionBound`. Weaker
conditions, such as those of red-black trees, bound the height by
`c * log₂ (N + 1)` for a constant `c`, and give the same class in `O(·)`.

The proof takes logarithms of `2 ^ height ≤ N + 1` with `Real.log_le_log` and
`Real.log_pow`, and divides by `log 2` with `le_div_iff₀`.
-/

noncomputable def bstSearchTimeFunctionBound (n : ℕ) : ℝ := Real.log (n + 1) / Real.log 2

theorem bstSearchTimeFunctionBound_correct {t : BinaryTree Nat} (target : Nat)
    (hd : 2 ^ t.height ≤ t.numNodes + 1) :
    ((bstSearchTM t target).time : ℝ) ≤ bstSearchTimeFunctionBound t.numNodes := by
  have h_time_le_height : (bstSearchTM t target).time ≤ t.height :=
    bstSearchTM_time_le_height t target
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

/-!
## The complexity class

The bound `log (n + 1) / log 2` is in `O(log n)`, with the constant `2 / log 2`
and the threshold `2`. For `n ≥ 2`, `n + 1 ≤ 2 * n`, so
`log (n + 1) ≤ log 2 + log n`, and `log 2 ≤ log n`. The tactic
`filter_upwards [eventually_ge_atTop 2] with n hn` reduces the statement for
all sufficiently large `n` to the statement at an arbitrary `n` with
`hn : n ≥ 2`.
-/

theorem bstSearchTimeFunctionBound_isBigO_logarithmic :
    bstSearchTimeFunctionBound ∈ O(Growth.logarithmic) := by
  refine IsBigO.of_bound (2 / Real.log 2) ?_
  filter_upwards [eventually_ge_atTop 2] with n hn
  have hn2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have h_log_mono := Real.log_le_log (by norm_num) hn2
  have h_log2_pos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  -- the goal is `‖bstSearchTimeFunctionBound n‖ ≤ 2 / Real.log 2 * ‖Growth.logarithmic n‖`
  simp only [bstSearchTimeFunctionBound, Growth.logarithmic, Real.norm_eq_abs]
  have h_log_np1_nonneg : (0 : ℝ) ≤ Real.log ((n : ℝ) + 1) := by
    apply Real.log_nonneg
    linarith
  have h_pos : (0 : ℝ) ≤ Real.log ((n : ℝ) + 1) / Real.log 2 := by positivity
  rw [abs_of_nonneg h_pos]
  have h_log_pos : (0 : ℝ) ≤ Real.log (n : ℝ) :=
    h_log_mono.trans' (Real.log_pos (by norm_num)).le
  rw [abs_of_nonneg h_log_pos]
  -- `n + 1 ≤ 2 * n` for `n ≥ 2`, so `log (n + 1) ≤ log 2 + log n`
  have h_np1_le : (n : ℝ) + 1 ≤ 2 * (n : ℝ) := by linarith
  have h_log_np1_le : Real.log ((n : ℝ) + 1) ≤ Real.log (2 * (n : ℝ)) :=
    Real.log_le_log (by linarith) h_np1_le
  have h_log_2n : Real.log (2 * (n : ℝ)) = Real.log 2 + Real.log (n : ℝ) :=
    Real.log_mul (by norm_num) (by positivity)
  rw [h_log_2n] at h_log_np1_le
  -- divide by `Real.log 2`, and bound the constant `1` by `log n / log 2 ≥ 1`
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
