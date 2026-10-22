import Mathlib

/-!
# Aronszajn Trees — Project Checkpoint
Initial testing and exploration of Mathlib definitions relevant
to trees of height omega-1, countable levels, and branches.
-/
namespace AronszajnTrees
#check Ordinal
#check Cardinal
#check Set.Countable


/-!
## Attempt 1: Defining a tree using a partial order
We know that in set theory, a tree is a partially ordered set where
the predecessors of any given node are well-ordered.
I want to start with this definition rather than introducing ordinals
immediately.
-/
#check PartialOrder
#check WellFounded

-- α represents the type of nodes in our tree.
-- The PartialOrder assumption tells Lean that
-- we have a relation ≤ on these nodes.

structure IsTreeOrder (α : Type*) [PartialOrder α] : Prop where
  -- There should be no infinite descending chains.
  wellFounded : WellFounded (fun s t : α => s < t)
  -- Any two strict predecessors of the same node must be comparable.
  predecessorsComparable :
    ∀ t s u : α,
      s < t →
      u < t →
      s ≤ u ∨ u ≤ s


/-!
## Testing the definition of a tree order
If we already know that α is a tree order, we should be able to
extract the fact that predecessors are comparable.
-/
example (α : Type*) [PartialOrder α]
    (h : IsTreeOrder α) (t s u : α)
    (hs : s < t) (hu : u < t) :
    s ≤ u ∨ u ≤ s := by
  exact h.predecessorsComparable t s u hs hu


/-!
## Understanding node heights and levels
I'm going to move onto defining node heights and levels.
I'll try to add a few more properties to the tree definition and
check mathlib definitions that have already been implemented.
-/
#check WellFounded.rank
#check WellFounded.rank_lt_of_rel
#check Ordinal
#check Ordinal.omega


/-!
## Node heights
We want to assign an ordinal to every node and Mathlib has
WellFounded.rank, which assigns an ordinal rank to elements
of a well-founded relation

Since our tree order is well-founded, we should be able to
use this to define the height of a node.
-/
noncomputable def nodeHeight {α : Type*} [PartialOrder α]
    (h : IsTreeOrder α) (t : α) : Ordinal := by
  -- Our tree definition contains a proof that <
  -- is well-founded. We make this available to Lean.
  letI : WellFounded (fun s u : α => s < u) :=
    h.wellFounded
  -- Now Mathlib can assign an ordinal rank to t.
  exact WellFounded.rank (fun s u : α => s < u) t


/-!
## Basic property of heights
If s is strictly below t in the tree, then
the height of s should be less than the height of t.
-/
theorem nodeHeight_lt_of_lt {α : Type*} [PartialOrder α]
    (h : IsTreeOrder α) {s t : α}
    (hst : s < t) :
    nodeHeight h s < nodeHeight h t := by
  -- Again, we're using the well-foundedness from our tree.
  let : WellFounded (fun x y : α => x < y) :=
    h.wellFounded
  -- Mathlib has the rank inequality we need!
  exact WellFounded.rank_lt_of_rel hst


/-!
## Levels of a tree
A level consists of all nodes having the same ordinal height.
For an ordinal β, level h β should be the set of nodes whose
height equals β.
-/
noncomputable def level {α : Type*} [PartialOrder α]
    (h : IsTreeOrder α) (β : Ordinal) : Set α :=
  {t | nodeHeight h t = β}

example {α : Type*} [PartialOrder α]
    (h : IsTreeOrder α) (β : Ordinal) (t : α) :
    t ∈ level h β ↔ nodeHeight h t = β := by
  rfl

end AronszajnTrees
