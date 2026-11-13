import AronszajnTrees.Checkpoint34

/-!
# An introduction
I realised I should probably have a file to record possible directions,
questions about Mathlib, and small statements I can test. Writing an `Is...`
predicate below doen't mean I have constructed an example satisfying it.

Current construction: increasing rational-valued functions on
ordinal initial segments, ordered by end-extension.

Final project goal: determine how much of an Aronszajn-tree
construction can be formalized (before the deadline)!
-/

namespace AronszajnTrees

/-!
## 1. What the rational-sequence approach has (and has not) established
A node has an ordinal length and a strictly increasing function
from that length into Q. Such a function is injective, so its
index type is countable.

This is different from saying that the set of all nodes at one
fixed length is countable. There might be uncountably many different
functions on a countable domain.

The intended construction should try to select countable sets of nodes
at each ordinal level, and make those selections compatible
with taking initial segments.
-/

#check RationalNode
#check RationalNode.length
#check EndExtends
#check rationalNode_domain_countable
#check CandidateLevel
#check PrefixClosedFamily
#check familyLevel
#check HasCountableSelectedLevels

/-!
## 2. Checking that end-extension really describes a tree order
If x is an initial segment of y, then x.length <= y.length and
the two functions agree at each index in the domain of x.

Already have:
* Reflexivity and transitivity of end-extension
* Restrictions of a node to shorter lengths
* Comparability of two initial segments of a common node

Still worth testing:
* Antisymmetry of end-extension
* An actual PartialOrder instance on RationalNode
* Well-foundedness of strict end-extension, using ordinal length
* Comparison between WellFounded.rank and the length of a node

A representation choice is whether to create a global PartialOrder
instance or to keep end-extension as an explicit relation while
these properties are proved.
-/

#check endExtends_refl
#check endExtends_trans
#check length_le_of_endExtends
#check restrictNode
#check restrictNode_endExtends
#check initialSegments_comparable
#check WellFounded

/-!
## 3. The extension problem at successor and limit stages
The intended selected family is prefix-closed, has nonempty levels
at every ordinal below omega_1, and has only countably many nodes
on each level.

At a successor ordinal, one tries to append a rational larger
than the previous values. At a limit ordinal, there is no last
stage: compatible shorter sequences must be combined.

A sequence can have every value below q while
approaching q, leaving no rational below q that can be appended.
For example, the rationals 1 - 1/(n+1) approach 1.

This motivates the HasRoomBelow condition: there must be some
p < q which still bounds all previous values, right?

Questions:
* How is HasRoomBelow preserved at successor stages?
* What additional compatibility is needed at countable limits?
* Can I enumerate all relevant (node, rational bound) pairs
  without making the next level uncountable?
* Can I prove a level-by-level extension invariant?
-/

#check BoundedAbove
#check boundedAbove_restrictNode
#check Ordinal.omega

/-!
## 4. Special trees and countable antichain colorings
A special Aronszajn tree can be written as a countable union
of antichains. One way to record this idea is with a coloring
into Nat, where different comparable nodes receive different
colors. The fibers of the coloring are then antichains.

This does not say the candidate family has such a coloring.
For the rational-sequence construction, finding a single useful
label for each node requires additional work: limit-length nodes
have no last rational entry to use as an obvious label.

I am recording the coloring condition separately so it can be
compared with a Suslin-style condition below.
-/

-- Distinct comparable nodes may not receive the same color.
def HasAntichainColoring (F : PrefixClosedFamily) : Prop :=
  ∃ color : RationalNode → ℕ,
    ∀ x y : RationalNode,
      x ∈ F.nodes → y ∈ F.nodes →
      x ≠ y → EndExtends x y → color x ≠ color y

-- This explicit notion avoids assuming a PartialOrder instance
-- has already been constructed for RationalNode.
def EndExtensionAntichain (a : Set RationalNode) : Prop :=
  ∀ x y : RationalNode,
    x ∈ a → y ∈ a → x ≠ y →
      ¬ EndExtends x y ∧ ¬ EndExtends y x

/-!
A small result I can establish now: if a coloring separates
comparable distinct nodes, then each fixed-color class is
an antichain. This is one direction of the connection between
countable colorings and special trees.
-/

theorem coloring_fiber_antichain
    (F : PrefixClosedFamily)
    (color : RationalNode → ℕ)
    (hcolor : ∀ x y : RationalNode,
      x ∈ F.nodes → y ∈ F.nodes →
      x ≠ y → EndExtends x y → color x ≠ color y)
    (n : ℕ) :
    EndExtensionAntichain
      {x | x ∈ F.nodes ∧ color x = n} := by
  intro x y hx hy hne
  constructor
  · intro hxy
    have hdiff : color x ≠ color y :=
      hcolor x y hx.1 hy.1 hne hxy
    exact hdiff (hx.2.trans hy.2.symm)
  · intro hyx
    have hdiff : color y ≠ color x :=
      hcolor y x hy.1 hx.1 (Ne.symm hne) hyx
    exact hdiff (hy.2.trans hx.2.symm)

/-!
## 5. Suslin trees are a different target
A Suslin tree at omega_1 has countable levels, no uncountable
chain, and no uncountable antichain. The last condition goes
beyond the Aronszajn requirements.

The existence of an Aronszajn tree is provable in ZFC, while
the existence of a Suslin tree is independent of ZFC (assuming
ZFC is consistent). So the Suslin condition is a comparison to
study maybe.

The following definitions are specifications only!
-/

def HasOnlyCountableAntichains (F : PrefixClosedFamily) : Prop :=
  ∀ a : Set RationalNode,
    a ⊆ F.nodes → EndExtensionAntichain a → a.Countable

def HasSuslinLikeConditions (F : PrefixClosedFamily) : Prop :=
  HasAronszajnConditions F ∧ HasOnlyCountableAntichains F

/-!
A fact to prove later, once the countability APIs are worked out:

If a family is uncountable and admits a countable antichain
coloring, then some color class must be uncountable. Otherwise
the family would be a countable union of countable sets.

In particular, a special Aronszajn tree cannot be a Suslin tree.
The coloring_fiber_antichain theorem above proves only the
antichain part, not the uncountability argument.
-/

#check Set.Countable
#check IsAntichain
#check Set.InjOn

/-!
## 6. Questions to revisit
1. Does my formal end-extension relation satisfy antisymmetry?
   The difficult Lean step is equality of functions whose domains
   are dependent subtypes of possibly different ordinal lengths.

2. What does PrefixClosedFamily actually guarantee? It records
   closure under restriction and boundedness, but neither the
   number of selected nodes nor the existence of a family with
   levels all the way through omega_1.

3. Can I produce an explicit rational specialization for the
   selected family, rather than only postulating one?

4. At a countable limit stage, how can compatible extensions be
   combined without exhausting the available rational upper bound?

5. If the complete existence construction remains unfinished,
   what is the strongest proved conditional result I can state?

Possible next tests in Lean?
* Complete antisymmetry and build a PartialOrder
* Show strict end-extension strictly increases ordinal length
* Show each chosen level is an antichain
* Show how a countable coloring produces countable chains
* Prove an extension lemma, then investigate limit stages
-/

end AronszajnTrees
