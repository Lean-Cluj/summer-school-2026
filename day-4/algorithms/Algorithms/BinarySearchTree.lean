/-
Copyright (c) 2026 Iulian Simion. All rights reserved.
Released under the 3-Clause BSD License as described in the file LICENSE.
Authors: Iulian Simion, assisted by Claude (Anthropic) and Gemini (Google)
-/
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Tree.Basic
import Mathlib.Order.Basic

/-!
# Binary search trees

A **binary tree** is either empty, or a node that holds a value and two binary
trees, its left and its right subtree. Mathlib defines the type
`BinaryTree α`, called `Tree α` in earlier versions of Mathlib, with two
constructors: `nil`, the empty tree, and `node v l r`, the node with value `v`,
left subtree `l` and right subtree `r`. When the expected type is
known to be a binary tree, `.nil` and `.node v l r` abbreviate
`BinaryTree.nil` and `BinaryTree.node v l r`.
-/

#print BinaryTree

/-!
A **binary search tree** is a binary tree in which, at every node, every value
in the left subtree is smaller than the value of the node, and every value in
the right subtree is larger. With these strict inequalities, a value occurs at
most once in the tree; some textbooks use `≤` and `≥` instead and allow repeated
values. To decide whether a value `x` occurs in a binary search tree, it
suffices to compare `x` with the value `v` at the root: if `x < v`, then `x` can
occur only in the left subtree, and if `x > v`, only in the right subtree. The
search follows a single path from the root and visits at most one node at each
distance from the root. At each node it makes at most two comparisons, first
`x == v` and then `x < v`.

## Implementation
-/

namespace BinaryTree

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

/-!
## Tests

The tree `myTree` below is a binary search tree:

```
      5
    /   \
   3     8
  / \   / \
 1   4 6   10
```
-/

def myTree : BinaryTree Nat :=
  .node 5
    (.node 3
      (.node 1 .nil .nil)
      (.node 4 .nil .nil))
    (.node 8
      (.node 6 .nil .nil)
      (.node 10 .nil .nil))

#eval bstSearch .nil 5      -- false
#eval bstSearch myTree 5    -- true
#eval bstSearch myTree 1    -- true
#eval bstSearch myTree 10   -- true
#eval bstSearch myTree 0    -- false
#eval bstSearch myTree 7    -- false
#eval bstSearch myTree 15   -- false

/-!
In the following tree, the value `7` is in the left subtree of `5`, so the tree
is not a binary search tree. The search compares `7` with `5`, continues in the
right subtree, and does not find `7`.
-/

#eval bstSearch (.node 5 (.node 7 .nil .nil) .nil) 7  -- false

/-!
## Specification

This file defines two inductive predicates on trees; Mathlib does not provide
them.

Membership in a tree is the predicate `Mem`, defined like `List.Mem`: a value
`x` is a member of `.node v l r` if it is `v`, or a member of `l`, or a member
of `r`. The empty tree has no members.

The invariant of binary search trees is the predicate `IsBST`.
The empty tree satisfies it, and `.node v l r` satisfies it when both subtrees
satisfy it, every member of `l` is smaller than `v`, and every member of `r` is
larger than `v`.
-/

inductive Mem (x : Nat) : BinaryTree Nat → Prop
  | here {l r} : Mem x (.node x l r)
  | left {v l r} : Mem x l → Mem x (.node v l r)
  | right {v l r} : Mem x r → Mem x (.node v l r)

inductive IsBST : BinaryTree Nat → Prop
  | nil : IsBST .nil
  | node {v l r} :
      IsBST l → IsBST r →
      (∀ y, Mem y l → y < v) → (∀ y, Mem y r → v < y) →
      IsBST (.node v l r)

/-!
The specification of the search has two parts.

* **Soundness**: if the search for `x` returns `true`, then `x` is a member of
  the tree.
* **Completeness**: if the tree is a binary search tree and `x` is a member,
  then the search for `x` returns `true`.

Soundness holds for every tree, since the search returns `true` only at a node
whose value is `x`. Completeness needs the invariant, as the last test above
shows.

## Soundness

The proof is by structural induction on the tree. In the case of a node, the
induction hypotheses `ih_l` and `ih_r` state soundness for the two subtrees.
-/

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
    · rw [h1]
      exact Mem.here
    · exact Mem.left (ih_l h)
    · exact Mem.right (ih_r h)

/-!
In the case of a node, the lemma `beq_iff_eq` replaces the Boolean comparison
`x == v` in `h` by the proposition `x = v`. The tactic
`split_ifs at h with h1 h2` then produces one goal for each of the three
branches of the two `if`s in `h`, and names the conditions `h1` and `h2`. In the
first goal, `h1 : x = v`, and `rw [h1]` turns the target into
`Mem v (.node v l r)`, which is the type of `Mem.here`. Without `beq_iff_eq`,
the condition would be `(x == v) = true`, which `rw` cannot use in this way.
-/

/-!
## Completeness

The proof is by structural induction on the tree, generalizing `x`, and in the
case of a node it takes the two hypotheses apart with `cases`. The hypothesis
`hbst` provides the invariant at the node, and `hmem` tells in which part of the
node `x` occurs.

* If `x` is in the left subtree, the invariant gives `x < v`. Hence
  `x = v` is false and `x < v` is true, and the search continues in the left
  subtree, where the induction hypothesis applies.
* If `x` is in the right subtree, the invariant gives `v < x`, and the search
  continues in the right subtree.
-/

-- The same theorem with the hypotheses before the colon; its proof is the proof
-- below without the line `intro hbst hmem`:
-- theorem mem_implies_bstSearch_true (t : BinaryTree Nat) (x : Nat)
--     (hbst : IsBST t) (hmem : Mem x t) : bstSearch t x = true := by
theorem mem_implies_bstSearch_true (t : BinaryTree Nat) (x : Nat) :
    IsBST t → Mem x t → bstSearch t x = true := by
  intro hbst hmem
  induction t generalizing x with
  | nil =>
    cases hmem
  | node v l r ih_l ih_r =>
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
        rw [if_neg hxv.ne', if_neg hxv.asymm]
        exact ih_r x hr hmr

/-!
The lemmas `if_pos` and `if_neg` evaluate an `if` whose condition is known to
be true or false. From `hxv : x < v`, the term `hxv.ne` proves `x ≠ v`; from
`hxv : v < x`, the term `hxv.ne'` proves `x ≠ v`, and `hxv.asymm` proves
`¬ x < v`.
-/

/-!
## Axioms

The soundness proof does not depend on `Classical.choice`, and the completeness
proof does. The axiom `Quot.sound` concerns quotient types; like `propext`, it
is not a principle of classical logic.
-/

#print axioms bstSearch_true_implies_mem  -- [propext, Quot.sound]
#print axioms mem_implies_bstSearch_true  -- [propext, Classical.choice, Quot.sound]

/-!
Both arguments use only case analysis, so the axiom comes from a tactic. In the
case `here`, the tactic `simp [bstSearch]` rewrites `x == x` to `true` with the
lemma `BEq.rfl`, which needs an instance stating that `==` is reflexive on `ℕ`.
Lean finds this instance through order instances of Mathlib, such as
`Nat.instTransOrd`, and these are proved with classical logic; the lemma
`BEq.rfl` itself depends on no axiom. The two theorems below prove the equation
of that case. The first uses `simp`. The second uses `simp only`, which rewrites
only with the lemmas it is given, and it does not depend on `Classical.choice`.

The command `#print axioms` therefore describes a proof, not a statement: the
same statement can have proofs that depend on different axioms.
-/

theorem bstSearch_node_self (x : Nat) (l r : BinaryTree Nat) :
    bstSearch (.node x l r) x = true := by
  simp [bstSearch]

theorem bstSearch_node_self' (x : Nat) (l r : BinaryTree Nat) :
    bstSearch (.node x l r) x = true := by
  simp only [bstSearch, beq_iff_eq, if_true]

#print axioms bstSearch_node_self   -- [propext, Classical.choice, Quot.sound]
#print axioms bstSearch_node_self'  -- [propext, Quot.sound]
#print axioms Nat.instTransOrd       -- [propext, Classical.choice, Quot.sound]

/-!
## Exercises

Solutions: `solutions/BinarySearchTree.lean`.
-/

/-! ### 1
Prove that `4` is a member of `myTree`. Write the proof as a term built from
the constructors of `Mem`. -/

theorem mem_four : Mem 4 myTree := sorry

/-! ### 2
Prove that, in a binary search tree, a search that returns `false` shows that
the value is not a member. -/

theorem not_mem_of_bstSearch_false (t : BinaryTree Nat) (x : Nat) (hbst : IsBST t)
    (h : bstSearch t x = false) : ¬ Mem x t := sorry

/-! ### 3
The function `bstInsert` inserts a value into a binary search tree: it adds a
leaf at the place where the search for the value ends, and it returns the tree
unchanged if the value is already in it. Prove that the inserted value is a
member of the result.

Hint: induction on `t`. After `unfold bstInsert`, the tactic `split_ifs` splits
the two `if`s. In the last case, `omega` proves `x = v`. -/

def bstInsert (t : BinaryTree Nat) (x : Nat) : BinaryTree Nat :=
  match t with
  | .nil => .node x .nil .nil
  | .node v l r =>
    if x < v then .node v (bstInsert l x) r
    else if v < x then .node v l (bstInsert r x)
    else t

#eval bstSearch (bstInsert myTree 7) 7  -- true

theorem mem_bstInsert (t : BinaryTree Nat) (x : Nat) : Mem x (bstInsert t x) := sorry

end BinaryTree
