/-
Copyright (c) 2026 Iulian Simion. All rights reserved.
Released under the 3-Clause BSD License as described in the file LICENSE.
Authors: Iulian Simion, assisted by Claude (Anthropic) and Gemini (Google)
-/
import Algorithms.BinarySearchTree

/-! # Solutions — Binary search trees -/

namespace BinaryTree.Solutions

-- 1
-- The value `4` is at the root of the right subtree of the left subtree.
theorem mem_four : Mem 4 myTree := Mem.left (Mem.right Mem.here)

-- 2
theorem not_mem_of_bstSearch_false (t : BinaryTree Nat) (x : Nat) (hbst : IsBST t)
    (h : bstSearch t x = false) : ¬ Mem x t := by
  intro hmem
  rw [mem_implies_bstSearch_true t x hbst hmem] at h
  contradiction

-- 3
theorem mem_bstInsert (t : BinaryTree Nat) (x : Nat) : Mem x (bstInsert t x) := by
  induction t with
  | nil => exact Mem.here
  | node v l r ih_l ih_r =>
    unfold bstInsert
    split_ifs with h1 h2
    · exact Mem.left ih_l
    · exact Mem.right ih_r
    · have hxv : x = v := by omega
      rw [hxv]
      exact Mem.here

end BinaryTree.Solutions
