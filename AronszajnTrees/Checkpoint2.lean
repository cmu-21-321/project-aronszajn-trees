import Mathlib
import AronszajnTrees.Checkpoint1

/-!
# Aronszajn Trees — Project Checkpoint 2
In the first checkpoint, I started defining tree orders,
node heights, levels, and some of the properties needed
for an Aronszajn tree. For this checkpoint, I want to work
with those definitions rather than introduce too many new ones.

In particular, I want to understand how the tree order
relates to chains and levels, and prove some of the
properties that we would expect mathematically.

I also want to test the definitions on a simpler example
before moving toward trees of height omega_1.
-/

namespace AronszajnTrees


/-!
## 1. Looking more closely at predecessors
In our definition of IsTreeOrder, we required the
predecessors of any node to be comparable.
I want to make the predecessor set explicit so that
I can prove things about it.

For a node t, its strict predecessors are all nodes s
such that s < t.
-/

def predecessors {α : Type*} [PartialOrder α]
    (t : α) : Set α :=
  {s | s < t}
-- Check the existing Mathlib definition of a chain.
#check IsChain
#check Set.Pairwise

/-!
A chain is a set whose elements are pairwise comparable.
The predecessor set should be a chain because our
tree definition already requires any two predecessors
of a node to be comparable.
-/

theorem predecessors_form_chain
    {α : Type*} [PartialOrder α]
    (h : IsTreeOrder α) (t : α) :
    IsChain (fun s u : α => s ≤ u) (predecessors t) := by
  -- Take two distinct nodes in the predecessor set.
  intro s hs u hu hne
  -- Both s and u are below t.
  -- Comparability is part of IsTreeOrder.
  exact h.predecessorsComparable t s u hs hu


/-!
## 2. Levels as antichains
Last time, I showed that two nodes at the same level
cannot be strictly below one another. Mathlib has a more
general definition for this: an antichain is a set in which
distinct elements are incomparable.

So each level of our tree should be an antichain.

I want to prove this using nodeHeight_lt_of_lt from Checkpoint 1.
-/

#check IsAntichain
#check lt_of_le_of_ne

theorem level_isAntichain
    {α : Type*} [PartialOrder α]
    (h : IsTreeOrder α) (β : Ordinal) :
    IsAntichain (fun s t : α => s ≤ t) (level h β) := by
  -- Take two distinct nodes on level β.
  intro s hs t ht hne hle
  -- If s ≤ t and s ≠ t, then s < t.
  have hst : s < t := lt_of_le_of_ne hle hne
  -- Heights must strictly increase along the tree order.
  have hrank : nodeHeight h s < nodeHeight h t :=
    nodeHeight_lt_of_lt h hst
  -- Both nodes have height β.
  change nodeHeight h s = β at hs
  change nodeHeight h t = β at ht
  -- This would give β < β, which is impossible.
  rw [hs, ht] at hrank
  exact (lt_irrefl β) hrank


/-!
## 3. How chains intersect levels
Now I want to connect the previous two results.

A chain consists of comparable nodes, but distinct
nodes on the same level are incomparable.
This means that a chain should intersect any level
in at most one node. Mathematically, if b is a chain and
T_β is a level, then b ∩ T_β has at most one element.

Mathlib expresses this using Set.Subsingleton.
-/

#check Set.Subsingleton
#check inter_subsingleton_of_isChain_of_isAntichain

/-!
Mathlib already has a theorem saying that the
intersection of a chain and an antichain is a
subsingleton.

Since we have proved that levels are antichains,
we can apply that result directly.
-/

theorem chain_meets_level_at_most_once
    {α : Type*} [PartialOrder α]
    (h : IsTreeOrder α)
    (β : Ordinal) (b : Set α)
    (hb : IsChain (fun s t : α => s ≤ t) b) :
    (b ∩ level h β).Subsingleton := by
  -- b is a chain by assumption.
  -- The level is an antichain by the previous theorem.
  have hlevel := level_isAntichain h β
  exact inter_subsingleton_of_isChain_of_isAntichain hb hlevel


/-!
## 4. Heights of different predecessors
I also want to understand what happens when we assign
ordinal heights to the predecessors of one node.
Since the predecessors form a chain, two distinct
predecessors should not have the same height.
In other words, nodeHeight should be injective when
restricted to the predecessor set.

This seems useful for understanding how the ordinal
rank corresponds to the order of predecessors.
-/

#check Set.InjOn

theorem predecessor_heights_injective
    {α : Type*} [PartialOrder α]
    (h : IsTreeOrder α) (t : α) :
    Set.InjOn (nodeHeight h) (predecessors t) := by
  -- Suppose s and u are predecessors of t
  -- with equal heights.
  intro s hs u hu heq
  -- Because they are predecessors of the same node,
  -- they must be comparable.
  rcases h.predecessorsComparable t s u hs hu with hsu | hus
  · -- First possibility: s ≤ u.
    -- If they were distinct, their heights would differ.
    by_contra hne
    have hlt : s < u := lt_of_le_of_ne hsu hne
    have hrank : nodeHeight h s < nodeHeight h u :=
      nodeHeight_lt_of_lt h hlt
    -- But we assumed their heights were equal.
    rw [heq] at hrank
    exact (lt_irrefl _) hrank
  · -- Second possibility: u ≤ s.
    -- We use the same argument in the other direction.
    by_contra hne
    have hlt : u < s := lt_of_le_of_ne hus (Ne.symm hne)
    have hrank : nodeHeight h u < nodeHeight h s :=
      nodeHeight_lt_of_lt h hlt
    rw [heq] at hrank
    exact (lt_irrefl _) hrank


/-!
## 5. Testing the definitions on a simpler tree
Before attempting an uncountable tree, I want to
check whether the definitions work for something
familiar.

The natural numbers with their usual order form a tree:
- The order is well-founded.
- The predecessors of n are 0, 1, ..., n-1.
- Any two natural numbers are comparable.

This is not an Aronszajn tree, since its height
is omega rather than omega_1, but it should be a
useful example for testing the definitions.
-/

#check Nat.lt_wfRel
#check Nat.lt_wfRel.wf

def natTreeOrder : IsTreeOrder Nat where
  -- The usual strict order on Nat is well-founded.
  wellFounded := Nat.lt_wfRel.wf
  -- The natural numbers are linearly ordered,
  -- so any two predecessors are comparable.
  predecessorsComparable := by
    intro t s u hs hu
    exact le_total s u


/-!
We can also show that all levels in this example
are countable. In fact, every subset of Nat is countable, so
we don't need to calculate the levels explicitly.
-/

theorem natTree_countable_levels :
    ∀ β : Ordinal, (level natTreeOrder β).Countable := by
  intro β
  -- Every subset of a countable type is countable.
  exact Set.to_countable (level natTreeOrder β)


/-!
## 6. Toward an Aronszajn tree construction
I have been looking at constructions using increasing sequences
of rational numbers. An important observation is that if a tree
has a function into Q which strictly increases along the
tree order, then no chain can be uncountable.

I want to formalize this independently of the construction,
so that it can be reused later.
-/

#check Set.InjOn
#check Set.countable_of_injective_of_countable_image

def HasRationalSpecialization
    {α : Type*} [PartialOrder α]
    (_h : IsTreeOrder α) : Prop :=
  ∃ f : α → ℚ,
    ∀ ⦃s t : α⦄, s < t → f s < f t

/-!
The idea is to restrict the function f to a chain.
Since any two distinct elements of a chain are
comparable, f must take different values on them.
Thus the chain injects into Q and is countable.
-/

theorem countable_chain_of_rational_specialization
    {α : Type*} [PartialOrder α]
    (h : IsTreeOrder α)
    (hspecial : HasRationalSpecialization h)
    (b : Set α)
    (hb : IsChain (fun s t : α => s ≤ t) b) :
    b.Countable := by
  obtain ⟨f, hf⟩ := hspecial
  -- Show that f is injective when restricted to b.
  have hinj : Set.InjOn f b := by
    intro s hs t ht heq
    by_contra hne
    -- Because b is a chain, s and t are comparable.
    rcases hb.total hs ht with hst | hts
    · have hlt : s < t := lt_of_le_of_ne hst hne
      exact (ne_of_lt (hf hlt)) heq
    · have hlt : t < s :=
        lt_of_le_of_ne hts (Ne.symm hne)
      exact (ne_of_lt (hf hlt)) heq.symm
  -- The image of b is a subset of the rationals.
  have himage : (f '' b).Countable :=
    Set.Countable.mono (Set.subset_univ _) Set.countable_univ
  -- An injection into a countable set gives countability.
  exact Set.countable_of_injective_of_countable_image hinj himage

/-!
## 7. What still needs to be formalized?
At this point we have proved some basic properties
that should hold for any tree order.

The next step is substantially harder because an
Aronszajn tree must have height omega_1, countable
levels, and no uncountable branch.

The natural-number example satisfies some of these
conditions, but it does not have the required height.

For the next steps in the project, I want to investigate
constructions of trees of height omega_1 and work
out which parts can be expressed using existing
Mathlib definitions.

In particular:

1. Investigate how to formalize the proposed rational-sequence
   construction of an omega_1-tree
2. Investigate how to represent nodes and extensions.
3. Determine how to prove each level is countable.
4. Understand how the construction prevents an
   uncountable/cofinal branch.

The main difficulty seems to be constructing an
actual example, rather than stating the Aronszajn
conditions themselves.

I also want to revisit whether WellFounded.rank is
the best way of defining heights, or whether using
order types of predecessor sets would make some of
the later arguments easier.
-/

#check Ordinal.omega
#check WellFounded.rank
#check WellFounded.mem_range_rank_of_le
#check IsMaxChain

end AronszajnTrees
