import AronszajnTrees.Checkpoint34

/-!
# Aronszajn Trees: From end-extension to a tree order
The previous checkpoint defined increasing ordinal-indexed rational
sequences and the relation EndExtends. Here I connect that concrete
relation with the abstract definition IsTreeOrder from Checkpoint 1.

The key is that a proper end-extension has a strictly larger
ordinal length. Since ordinals are well-ordered, we cannot have an
infinite descending sequence of proper end-extensions.

These results concern the ambient tree of rational sequences.
They do not construct the countable selected levels required for
an Aronszajn tree.
-/

namespace AronszajnTrees

/-!
## 1. Equal-length end-extensions are equal
If x is an initial segment of y, but both have the same domain,
then their values agree at every index. Hence they are the same node.
-/

theorem endExtends_eq_of_length_eq
    {x y : RationalNode}
    (hxy : EndExtends x y)
    (hlen : x.length = y.length) : x = y := by
  cases x with
  | mk lx fx hx =>
    cases y with
    | mk ly fy hy =>
      change lx = ly at hlen
      subst ly
      have hvalues : fx = fy := by
        funext i
        have hi := hxy.2 i
        simpa using hi
      subst fy
      rfl

/-!
## 2. Antisymmetry
End-extension in both directions forces the two lengths to be
equal. We can then use the previous result.
-/

theorem endExtends_antisymm
    {x y : RationalNode}
    (hxy : EndExtends x y)
    (hyx : EndExtends y x) : x = y := by
  apply endExtends_eq_of_length_eq hxy
  exact le_antisymm hxy.1 hyx.1

/-!
## 3. The partial order on rational nodes
The order x ≤ y means that x is an initial segment of y.
Reflexivity and transitivity were proved in Checkpoint34.
Antisymmetry was the missing piece.
-/

instance : PartialOrder RationalNode where
  le := EndExtends
  le_refl := endExtends_refl
  le_trans := by
    intro x y z hxy hyz
    exact endExtends_trans hxy hyz
  le_antisymm := by
    intro x y hxy hyx
    exact endExtends_antisymm hxy hyx

/-!
## 4. Proper end-extension increases ordinal length
If x < y, then x ≤ y, hence length x ≤ length y.
Equality of lengths would force x = y, contradicting x < y.
-/

theorem length_lt_of_lt
    {x y : RationalNode} (hxy : x < y) :
    x.length < y.length := by
  have hle : EndExtends x y := le_of_lt hxy
  apply lt_of_le_of_ne hle.1
  intro heq
  have hnodes : x = y := endExtends_eq_of_length_eq hle heq
  exact (ne_of_lt hxy) hnodes

/-!
## 5. End-extension defines a tree order

The length map sends every strictly smaller node to a strictly
smaller ordinal. Therefore the strict order on RationalNode is
well-founded. Also, any two predecessors of a given node are
comparable by initialSegments_comparable from Checkpoint34.
-/

theorem rationalNodes_form_tree : IsTreeOrder RationalNode where
  wellFounded := by
    apply Subrelation.wf
      (h₂ := InvImage.wf RationalNode.length Ordinal.lt_wf)
    intro x y hxy
    exact length_lt_of_lt hxy
  predecessorsComparable := by
    intro t s u hs hu
    exact initialSegments_comparable (le_of_lt hs) (le_of_lt hu)

/-!
## What remains
This theorem proves that the ambient rational-sequence order is
a tree but it doesn't establish that its levels are countable.
The next mathematical task is to find a coherent prefix-closed
subfamily with countably many nodes at each level below omega_1.
-/

end AronszajnTrees
