import AronszajnTrees.Checkpoint34
import AronszajnTrees.ConstructionOrder

/-!
# Aronszajn Trees — No Cofinal Branches
The end-extension relation is now a tree order. Here I want to prove
something that is specific to the rational-sequence construction:
there cannot be a chain with nodes extending arbitrarily far through
all the countable ordinals.

The idea is to suppose that we have such a chain b. At every ordinal
index below a target ordinal, choose a sufficiently long sequence in b
and read its rational value at that index. Since the sequences form a
chain, they agree on their shared initial segments. The resulting
function into Q is strictly increasing, and hence injective.

For the target omega_1, this contradicts its uncountability.

This proof concerns the ambient tree. We do NOT need to have selected
countable levels yet.
-/

namespace AronszajnTrees

/-!
## 1. Theorem about ordinal lengths
We first work with an arbitrary ordinal `limit`. If a chain has a node
longer than each index below `limit`, then those indices inject into Q.
In particular, the index type must be countable.

This general statement makes it easier to isolate the construction
argument from the specific cardinality of omega_1.
-/

theorem countable_below_of_strictly_cofinal_chain
    (limit : Ordinal) (b : Set RationalNode)
    (hchain : IsEndExtensionChain b)
    (hcofinal : ∀ β : Ordinal, β < limit →
      ∃ x : RationalNode, x ∈ b ∧ β < x.length) :
    Countable {β : Ordinal // β < limit} := by
  classical
  -- For every index choose a node whose domain contains it.
  let pick : {β : Ordinal // β < limit} → RationalNode :=
    fun i => Classical.choose (hcofinal i.val i.property)
  have hpick (i : {β : Ordinal // β < limit}) :
      pick i ∈ b ∧ i.val < (pick i).length := by
    change (Classical.choose (hcofinal i.val i.property)) ∈ b ∧
      i.val < (Classical.choose (hcofinal i.val i.property)).length
    exact Classical.choose_spec (hcofinal i.val i.property)
  -- Read the rational at index i from the chosen node.
  let f : {β : Ordinal // β < limit} → ℚ :=
    fun i => (pick i).values ⟨i.val, (hpick i).2⟩
  -- The choice of a particular node does not cause a conflict:
  -- any two nodes in the chain agree on their overlap.
  have hf : StrictMono f := by
    intro i j hij
    have hindex : i.val < j.val := hij
    rcases hchain (pick i) (hpick i).1 (pick j) (hpick j).1 with hxy | hyx
    · -- The node chosen for i is an initial segment of that for j.
      have hi : i.val < (pick j).length :=
        lt_of_lt_of_le (hpick i).2 hxy.1
      have hlt :
          (pick j).values ⟨i.val, hi⟩ <
          (pick j).values ⟨j.val, (hpick j).2⟩ := by
        apply (pick j).increasing
        exact hindex
      calc
        f i = (pick i).values ⟨i.val, (hpick i).2⟩ := rfl
        _ = (pick j).values ⟨i.val, hi⟩ := hxy.2 _
        _ < (pick j).values ⟨j.val, (hpick j).2⟩ := hlt
        _ = f j := rfl
    · -- Or the node chosen for j is an initial segment of that for i.
      have hj : j.val < (pick i).length :=
        lt_of_lt_of_le (hpick j).2 hyx.1
      have hlt :
          (pick i).values ⟨i.val, (hpick i).2⟩ <
          (pick i).values ⟨j.val, hj⟩ := by
        apply (pick i).increasing
        exact hindex
      calc
        f i = (pick i).values ⟨i.val, (hpick i).2⟩ := rfl
        _ < (pick i).values ⟨j.val, hj⟩ := hlt
        _ = (pick j).values ⟨j.val, (hpick j).2⟩ := (hyx.2 _).symm
        _ = f j := rfl
  -- A strictly increasing function into the countable type Q
  -- is injective. Thus its domain must be countable.
  exact hf.injective.countable

/-!
## 2. Omega_1 has uncountably many predecessors
To use the general result, we need to know that the ordinals below
omega_1 are not countable. Their cardinality is aleph_1, which is
strictly larger than aleph_0.
-/

private theorem not_countable_below_omega_one :
    ¬ Countable {β : Ordinal // β < Ordinal.omega 1} := by
  intro hcount
  letI : Countable {β : Ordinal // β < Ordinal.omega 1} := hcount
  have hle :
      Cardinal.mk {β : Ordinal // β < Ordinal.omega 1} ≤ Cardinal.aleph0 :=
    Cardinal.mk_le_aleph0
  have hbad : (Cardinal.aleph 1 : Cardinal.{1}) ≤ Cardinal.aleph0 := by
    simpa only [Ordinal.cardinalMk_Iio, Ordinal.card_omega,
      Cardinal.lift_aleph, Ordinal.lift_one] using hle
  exact (not_le.mpr Cardinal.aleph0_lt_aleph_one) hbad

/-!
## 3. No chain is cofinal in omega_1
To read the value at beta, we need a strictly longer
node. We obtain one by applying the cofinality assumption at the
successor of beta; omega_1 is a limit ordinal.
-/

theorem ambient_no_cofinal_chain :
    ¬ ∃ b : Set RationalNode,
      IsEndExtensionChain b ∧
      (∀ β : Ordinal, β < Ordinal.omega 1 →
        ∃ x : RationalNode, x ∈ b ∧ β ≤ x.length) := by
  rintro ⟨b, hchain, hcofinal⟩
  have hstrict : ∀ β : Ordinal, β < Ordinal.omega 1 →
      ∃ x : RationalNode, x ∈ b ∧ β < x.length := by
    intro β hβ
    have hsucc : Order.succ β < Ordinal.omega 1 :=
      (Cardinal.isSuccLimit_omega 1).succ_lt hβ
    obtain ⟨x, hxb, hxlen⟩ := hcofinal (Order.succ β) hsucc
    exact ⟨x, hxb, lt_of_lt_of_le (lt_succ β) hxlen⟩
  exact not_countable_below_omega_one
    (countable_below_of_strictly_cofinal_chain
      (Ordinal.omega 1) b hchain hstrict)

/-!
## 4. Consequences for the selected family
Any family of our rational nodes already satisfies the no-cofinal-branch
property, whether or not we have worked out its countable-level construction.
-/

theorem selected_family_no_cofinal_chain (F : PrefixClosedFamily) :
    HasNoCofinalEndExtensionChain F := by
  intro h
  obtain ⟨b, _hsubset, hchain, hcofinal⟩ := h
  exact ambient_no_cofinal_chain ⟨b, hchain, hcofinal⟩

/-!
## 5. Reducing the final existence proof
If we actually construct a prefix-closed family of height omega_1
with countable selected levels, we will not have to reprove the
absence of cofinal branches. That part now follows from the ambient
tree argument.

This is a conditional theorem, not a construction of such a family.
-/

theorem aronszajn_of_height_and_countable_levels
    (F : PrefixClosedFamily)
    (hheight : HasHeightOmegaOneByLength F)
    (hlevels : HasCountableSelectedLevels F) :
    HasAronszajnConditions F := by
  exact ⟨hheight, hlevels, selected_family_no_cofinal_chain F⟩

/-!
The no-cofinal-branch condition is now handled by the choice of Q.
The main unfinished part of the project is the actual construction
of a prefix-closed family with nonempty, countable selected levels
at every beta below omega_1, especially at countable limit stages.
-/

end AronszajnTrees
