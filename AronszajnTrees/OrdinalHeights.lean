import AronszajnTrees.ConstructionOrder

/-!
# Initial Segments and Ordinal Lengths
In Checkpoint34, I defined nodes with ordinal lengths and a restriction
operation. ConstructionOrder proved that end-extension gives a tree order.
Here I want to understand the predecessors of an individual node more
explicitly, before trying to identify Mathlib's WellFounded.rank with
its ordinal length.

The immediate goal is to show that an initial segment of y is uniquely
determined by its length. This is the mathematical reason the predecessors
of y have the same order structure as the ordinals below y.length.
-/

namespace AronszajnTrees

/-!
## 1. Every initial segment is a restriction
Suppose x is an initial segment of y. Restricting y to x.length
should give back x. The proof uses equal-length end-extensions,
which we established in ConstructionOrder.
-/

theorem endExtends_eq_restrict
    {x y : RationalNode} (hxy : EndExtends x y) :
    x = restrictNode y x.length hxy.1 := by
  apply endExtends_eq_of_length_eq
  · refine ⟨le_refl _, ?_⟩
    intro i
    exact hxy.2 i
  · rfl

/-!
## 2. Two initial segments of equal length are equal
This lets us describe each level below a fixed node without
choosing a particular representation of its predecessor set.
-/

theorem initialSegments_eq_of_length_eq
    {x y z : RationalNode}
    (hx : EndExtends x z) (hy : EndExtends y z)
    (hlen : x.length = y.length) : x = y := by
  rcases initialSegments_comparable hx hy with hxy | hyx
  · exact endExtends_eq_of_length_eq hxy hlen
  · exact (endExtends_eq_of_length_eq hyx hlen.symm).symm

/-!
## 3. Length strictly increases along proper end-extension
This is the important order-theoretic connection we already proved.
Here we record a useful consequence: if two comparable nodes have
identical lengths, they must be the same node.
-/

theorem comparable_eq_of_length_eq
    {x y : RationalNode}
    (hxy : x ≤ y ∨ y ≤ x)
    (hlen : x.length = y.length) : x = y := by
  rcases hxy with hxy | hyx
  · exact endExtends_eq_of_length_eq hxy hlen
  · exact (endExtends_eq_of_length_eq hyx hlen.symm).symm

/-!
## 4. What remains for a full ordinal-height theorem
For a fixed node y, the map that is:

   β ↦ restrictNode y β (proof that β ≤ y.length)

parametrizes all initial segments of y. We have proved uniqueness
of a prefix at each length, and ConstructionOrder proves that proper
extension increases ordinal length.

Next I want to formalize an order isomorphism between the strict
predecessors of y and the ordinal interval {β // β < y.length}.
Such an equivalence is the natural route to proving:

   nodeHeight rationalNodes_form_tree y = y.length.

This equivalence and rank equality are still proof obligations.
-/

#check WellFounded.rank
#check OrderIso
#check Ordinal.type

end AronszajnTrees
