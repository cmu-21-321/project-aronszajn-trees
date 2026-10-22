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
  letI : WellFounded (fun x y : α => x < y) :=
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


/-!
## Nodes on the same level
I want to prove that two nodes on the same level cannot be
strictly comparable. This should follow from the previous theorem
about node heights, since being on the same level means that
both nodes have the same ordinal height.
-/
theorem same_level_not_lt {α : Type*} [PartialOrder α]
    (h : IsTreeOrder α) (β : Ordinal) {s t : α}
    (hs : s ∈ level h β)
    (ht : t ∈ level h β) :
    ¬ s < t := by
  -- Suppose s < t.
  intro hst
  -- From our earlier theorem, the height of s
  -- must be strictly smaller than that of t.
  have hheight : nodeHeight h s < nodeHeight h t :=
    nodeHeight_lt_of_lt h hst
  -- Unpack what membership in level β means.
  change nodeHeight h s = β at hs
  change nodeHeight h t = β at ht
  -- Both heights are β, which gives β < β.
  rw [hs, ht] at hheight
  exact (lt_irrefl β) hheight


/-!
## Countable levels
One of the main conditions in the definition of an Aronszajn
tree is that every level must be countable. Mathlib already has
Set.Countable, so I want to express this condition using our
earlier definition of a level.
For now, this is just a property that a tree may satisfy,
rather than something true of all trees.
-/
#check Set.Countable

def HasCountableLevels {α : Type*} [PartialOrder α]
    (h : IsTreeOrder α) : Prop :=
  ∀ β : Ordinal, (level h β).Countable


/-!
## Initial exploration of branches
Another important condition for an Aronszajn tree is that it
has no uncountable branches. A branch is a maximal chain, so
I want to start by understanding Mathlib's definition of a chain.
A chain is a set of nodes where any two elements are comparable
under the tree order.
-/
#check IsChain
#check IsMaxChain
#check Set.Countable

-- First, define what it means for a set of nodes
-- to be a chain in our partial order.
def IsTreeChain {α : Type*} [PartialOrder α]
    (_h : IsTreeOrder α) (b : Set α) : Prop :=
  IsChain (fun s t : α => s ≤ t) b

-- If every chain is countable, then there cannot be an
-- uncountable branch. I'll just use this formulation
-- since it avoids having to formalize maximality immediately.
def HasOnlyCountableChains {α : Type*} [PartialOrder α]
    (h : IsTreeOrder α) : Prop :=
  ∀ b : Set α, IsTreeChain h b → b.Countable


/-!
## Trees of height omega_1
An Aronszajn tree must have height omega_1. There are two
conditions I want to express:
1. Every node has height strictly below omega_1.
2. Every ordinal below omega_1 occurs as the
   height of some node.
Together, these describe a tree whose levels extend through
all countable ordinals.
-/
#check Ordinal.omega
#check Ordinal.omega0

def HasHeightOmegaOne {α : Type*} [PartialOrder α]
    (h : IsTreeOrder α) : Prop :=
  (∀ t : α, nodeHeight h t < Ordinal.omega 1) ∧
  (∀ β : Ordinal,
    β < Ordinal.omega 1 → (level h β).Nonempty)


/-!
## Tentative definition of an Aronszajn tre
Combining the properties defined above, we can try to state
what it means for our tree order to be an Aronszajn tree.
Honestly there's probably still better existing Mathlib
abstractions to use, particularly for representing tree height.
So, this is a tentative definition, and I expect to refine it.
-/
def IsAronszajn {α : Type*} [PartialOrder α]
    (h : IsTreeOrder α) : Prop :=
  HasHeightOmegaOne h ∧
  HasCountableLevels h ∧
  HasOnlyCountableChains h

end AronszajnTrees
