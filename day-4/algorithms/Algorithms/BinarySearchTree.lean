import Mathlib.Data.Nat.Basic
import Mathlib.Data.Tree.Basic
import Mathlib.Order.Basic


namespace BinaryTree


----------------------------------------------------------------------------------------------------
-- Check that an elment is present in a Binary Search Tree (BST)
----------------------------------------------------------------------------------------------------


def bstSearch (t : BinaryTree Nat) (target : Nat) : Bool :=
  match t with
  | .nil => false
  | .node v l r =>
    if target == v then
      true
    else if target < v then
      bstSearch l target
    else
      bstSearch r target


----------------------------------------------------------------------------------------------------
-- Concrete Examples
----------------------------------------------------------------------------------------------------


-- Sample Binary Search Tree for testing
--       5
--     /   \
--    3     8
--   / \   / \
--  1   4 6   10
def myTree : BinaryTree Nat :=
  .node 5
    (.node 3
      (.node 1 .nil .nil)
      (.node 4 .nil .nil))
    (.node 8
      (.node 6 .nil .nil)
      (.node 10 .nil .nil))


#eval bstSearch .nil 5
-- Output: false

#eval bstSearch myTree 5
-- Output: true

#eval bstSearch myTree 1
-- Output: true

#eval bstSearch myTree 10
-- Output: true

#eval bstSearch myTree 0
-- Output: false

#eval bstSearch myTree 7
-- Output: false

#eval bstSearch myTree 15
-- Output: false


----------------------------------------------------------------------------------------------------
-- Formal Verification
----------------------------------------------------------------------------------------------------

inductive Mem (x : Nat) : BinaryTree Nat → Prop
  | here {l r} : Mem x (.node x l r)
  | left {v l r} : Mem x l → Mem x (.node v l r)
  | right {v l r} : Mem x r → Mem x (.node v l r)

/-- The binary search tree invariant: every value in the left subtree is smaller than the
root, every value in the right subtree is larger, and both subtrees are themselves BSTs. -/
inductive IsBST : BinaryTree Nat → Prop
  | nil : IsBST .nil
  | node {v l r} :
      IsBST l → IsBST r →
      (∀ y, Mem y l → y < v) → (∀ y, Mem y r → v < y) →
      IsBST (.node v l r)

-- Soundness
theorem bstSearch_true_implies_mem (t : BinaryTree Nat) (x : Nat) :
    bstSearch t x = true → Mem x t := by
  induction t with
  | nil =>
    intro h
    simp [bstSearch] at h
  | node v l r ih_l ih_r =>
    intro h
    simp only [bstSearch, beq_iff_eq] at h
    split_ifs at h with h1 h2
    · subst h1
      exact Mem.here
    · exact Mem.left (ih_l h)
    · exact Mem.right (ih_r h)

-- Completeness
theorem mem_implies_bstSearch_true (t : BinaryTree Nat) (x : Nat) :
    IsBST t → Mem x t → bstSearch t x = true := by
  revert x
  induction t with
  | nil =>
    intro x _ hmem
    cases hmem
  | node v l r ih_l ih_r =>
    intro x hbst hmem
    cases hbst with
    | node hl hr hlt hgt =>
      cases hmem with
      | here =>
        simp [bstSearch]
      | left hml =>
        have hxv : x < v := hlt x hml
        simp only [bstSearch, beq_iff_eq]
        rw [if_neg hxv.ne, if_pos hxv]
        exact ih_l x hl hml
      | right hmr =>
        have hxv : v < x := hgt x hmr
        simp only [bstSearch, beq_iff_eq]
        rw [if_neg hxv.ne', if_neg (by omega : ¬ x < v)]
        exact ih_r x hr hmr



end BinaryTree
