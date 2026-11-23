import AronszajnTrees.ConstructionOrder

/-!
# Aronszajn Trees — First Steps in Level Construction
The earlier checkpoints defined a selected prefix-closed family and
specified an extension invariant. The missing mathematical work is
constructing such a family with countable levels all the way to ω₁.

I am starting with the successor step: given an increasing rational
sequence whose old values have room below q, append one rational and
preserve some room below q. This does not solve the limit-ordinal
step, which requires combining countably many compatible extensions.

A second experiment constructs the family of all initial segments
of one node. It has countable levels, but its height is bounded by
that node's length. This shows exactly why countable levels alone
are not enough for an Aronszajn tree.
-/

namespace AronszajnTrees

/-!
## 1. Append one rational at a successor length
Assume every value of x is strictly below p. We can append p at
index x.length. The new length is the successor of x.length.
-/

noncomputable def appendRational (x : RationalNode) (p : ℚ)
    (hp : ∀ i, x.values i < p) : RationalNode := by
  classical
  refine {
    length := Order.succ x.length
    values := fun i =>
      if hi : i.val < x.length then x.values ⟨i.val, hi⟩ else p
    increasing := ?_
  }
  intro i j hij
  have hij' : i.val < j.val := hij
  by_cases hi : i.val < x.length
  · by_cases hj : j.val < x.length
    · have hlt :
          x.values ⟨i.val, hi⟩ < x.values ⟨j.val, hj⟩ := by
        apply x.increasing
        exact hij'
      simpa [hi, hj] using hlt
    · have hlt : x.values ⟨i.val, hi⟩ < p := hp _
      simpa [hi, hj] using hlt
  · -- There cannot be two distinct indices at or above x.length
    -- but strictly below its immediate successor.
    have hle : x.length ≤ i.val := le_of_not_gt hi
    have hgt : x.length < j.val := lt_of_le_of_lt hle hij'
    have hjle : j.val ≤ x.length := Order.le_of_lt_succ j.property
    exact absurd hgt (not_lt_of_ge hjle)

/-!
The original sequence is an initial segment of the appended one.
-/

theorem endExtends_appendRational
    (x : RationalNode) (p : ℚ)
    (hp : ∀ i, x.values i < p) :
    EndExtends x (appendRational x p hp) := by
  refine ⟨Order.le_succ _, ?_⟩
  intro i
  simp [appendRational, i.property]

/-!
## 2. Preserve the available rational bound
HasRoomBelow x q gives a rational p < q above every old entry.
Append p. Density of the rationals gives r with p < r < q, so
the longer sequence still has room below q.

This is a genuine successor-stage extension lemma. It does not
address how to pass through a countable limit ordinal.
-/

theorem successor_extension_with_room
    (x : RationalNode) (q : ℚ)
    (hroom : HasRoomBelow x q) :
    ∃ y : RationalNode,
      y.length = Order.succ x.length ∧
      EndExtends x y ∧ HasRoomBelow y q := by
  classical
  obtain ⟨p, hpq, hp⟩ := hroom
  refine ⟨appendRational x p hp, rfl,
    endExtends_appendRational x p hp, ?_⟩
  obtain ⟨r, hpr, hrq⟩ := exists_between hpq
  refine ⟨r, hrq, ?_⟩
  intro i
  by_cases hi : i.val < x.length
  · have hlt : x.values ⟨i.val, hi⟩ < r :=
      lt_trans (hp _) hpr
    simpa [appendRational, hi] using hlt
  · simpa [appendRational, hi] using hpr

/-!
## 3. An actual prefix-closed family from one node
The set of initial segments of a bounded node is automatically
prefix-closed. Its levels contain at most one element, so they are
countable. This is a concrete example of our general definitions,
although it is not tall enough to be an Aronszajn tree.
-/

def initialSegmentsFamily (x : RationalNode)
    (hx : BoundedAbove x) : PrefixClosedFamily where
  nodes := {y | EndExtends y x}
  bounded := by
    intro y hy
    obtain ⟨q, hq⟩ := hx
    refine ⟨q, ?_⟩
    intro i
    rw [hy.2 i]
    exact hq ⟨i.val, lt_of_lt_of_le i.property hy.1⟩
  prefix_closed := by
    intro y hy β hβ
    exact endExtends_trans (restrictNode_endExtends y β hβ) hy

theorem initialSegmentsFamily_level_subsingleton
    (x : RationalNode) (hx : BoundedAbove x)
    (β : Ordinal) :
    (familyLevel (initialSegmentsFamily x hx) β).Subsingleton := by
  intro a ha b hb
  change EndExtends a x ∧ a.length = β at ha
  change EndExtends b x ∧ b.length = β at hb
  rcases initialSegments_comparable ha.1 hb.1 with hab | hba
  · exact endExtends_eq_of_length_eq hab (ha.2.trans hb.2.symm)
  · exact (endExtends_eq_of_length_eq hba (hb.2.trans ha.2.symm)).symm

theorem initialSegmentsFamily_countable_levels
    (x : RationalNode) (hx : BoundedAbove x) :
    HasCountableSelectedLevels (initialSegmentsFamily x hx) := by
  intro β
  exact (initialSegmentsFamily_level_subsingleton x hx β).countable

theorem initialSegmentsFamily_nonempty_below
    (x : RationalNode) (hx : BoundedAbove x)
    (β : Ordinal) (hβ : β ≤ x.length) :
    (familyLevel (initialSegmentsFamily x hx) β).Nonempty := by
  refine ⟨restrictNode x β hβ, ?_⟩
  exact ⟨restrictNode_endExtends x β hβ, rfl⟩

/-!
## 4. Using the extension invariant
The checkpoint already specified HasExtensionInvariant.
If there is a selected root at length zero with room below q,
then that invariant forces every countable ordinal level to be
nonempty. The theorem below tells us precisely what the eventual
recursive construction needs to provide.
-/

theorem nonempty_levels_of_extension_invariant
    (F : PrefixClosedFamily)
    (hroot : ∃ x : RationalNode,
      x ∈ familyLevel F 0 ∧ ∃ q : ℚ, HasRoomBelow x q)
    (hext : HasExtensionInvariant F) :
    ∀ β : Ordinal, β < Ordinal.omega 1 →
      (familyLevel F β).Nonempty := by
  intro β hβ
  obtain ⟨x, hx, q, hroom⟩ := hroot
  by_cases hzero : β = 0
  · subst β
    exact ⟨x, hx⟩
  · have hpos : (0 : Ordinal) < β := by
      exact lt_of_le_of_ne zero_le (Ne.symm hzero)
    obtain ⟨y, hy, _, _⟩ := hext 0 β hpos hβ x hx q hroom
    exact ⟨y, hy⟩

/-!
## Remaining obstacle: the countable limit stage
The successor-extension lemma does not solve the full existence
problem. At a countable limit ordinal γ, we need to take a union
of a coherent chain of extensions whose lengths approach γ.
We then need to prove the union still has room below a rational
bound, and choose only countably many such unions at each level.

These are the main next proof obligations:
1. Construct compatible extensions along a cofinal Nat-sequence.
2. Define their union as a RationalNode of length γ.
3. Preserve strict monotonicity and HasRoomBelow.
4. Prove countability of the collection selected at level γ.

Neither the preceding example nor the extension invariant theorem
proves that a suitable height-ω₁ family actually exists.
-/

end AronszajnTrees
