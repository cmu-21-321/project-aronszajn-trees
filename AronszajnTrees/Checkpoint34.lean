import AronszajnTrees.Checkpoint1

/-!
# Aronszajn Trees — Combined Checkpoints 3 and 4
I was sick last week, so I am combining the two checkpoints into one file. The
earlier checkpoints developed the basic definitions of tree orders,
predecessors, levels, and chains. This file develops a concrete model of
increasing rational sequences indexed by ordinals, and the end-extension
relation on them.

I'm now trying to build a concrete example rather than just state
those conditions.

## Mathematical plan (to justify, not just implement)
I am investigating the classical rational-sequence construction
(see Jech, Set Theory, Theorem 9.16). A node is an increasing
ordinal-indexed rational sequence. The order is end-extension.

The choice of rationals matters: no strictly increasing sequence
of rationals can have length omega_1. Consequently a cofinal branch
of such sequences should be impossible. This still requires a proof
in our formal model; the definition alone does not establish it.

The real obstruction isn't the countability of an individual
sequence's domain. It's more about selecting a countable collection
of nodes at each ordinal level, while making the selected levels compatible.

The decisions I want to test here are:
1. Is an ordinal-indexed function a convenient representation of a node?
2. Does end-extension capture the predecessor relation correctly?
3. What extra invariant would let us choose countable levels
   at successor and limit stages?

So in this file we formalize the first two questions and gives an exact
statement of the third. We are not claiming to construct the final
tree yet!
-/

namespace AronszajnTrees

/-!
## Part I (Checkpoint 3): Ordinal-indexed rational sequences
A node carries its length as an ordinal and its values as a function
on the ordinals below that length. The subtype makes the domain
explicit, rather than evaluating a sequence at invalid indices.
-/

#check Ordinal
#check Ordinal.omega
#check StrictMono
#check Set.Countable

structure RationalNode where
  length : Ordinal
  values : {i : Ordinal // i < length} → ℚ
  increasing : StrictMono values

-- This just unpacks the strict-monotonicity assumption.
theorem rationalNode_values_increase
    (x : RationalNode)
    {i j : {k : Ordinal // k < x.length}}
    (hij : i < j) : x.values i < x.values j := by
  exact x.increasing hij

/-!
## End-extension
x is an initial segment of y if x is no longer than y and
all entries already defined in x agree with those in y.
-/

def EndExtends (x y : RationalNode) : Prop :=
  ∃ h : x.length ≤ y.length,
    ∀ i : {k : Ordinal // k < x.length},
      x.values i =
        y.values ⟨i.val, lt_of_lt_of_le i.property h⟩

theorem endExtends_refl (x : RationalNode) :
    EndExtends x x := by
  refine ⟨le_refl _, ?_⟩
  intro i
  rfl

theorem length_le_of_endExtends
    {x y : RationalNode} (hxy : EndExtends x y) :
    x.length ≤ y.length := by
  exact hxy.1

theorem endExtends_trans
    {x y z : RationalNode}
    (hxy : EndExtends x y) (hyz : EndExtends y z) :
    EndExtends x z := by
  obtain ⟨hxyLen, hxyValues⟩ := hxy
  obtain ⟨hyzLen, hyzValues⟩ := hyz
  refine ⟨le_trans hxyLen hyzLen, ?_⟩
  intro i
  calc
    x.values i =
        y.values ⟨i.val, lt_of_lt_of_le i.property hxyLen⟩ :=
          hxyValues i
    _ = z.values
        ⟨i.val, lt_of_lt_of_le i.property (le_trans hxyLen hyzLen)⟩ :=
          hyzValues ⟨i.val, lt_of_lt_of_le i.property hxyLen⟩

/-!
## Countability of the domain
Because the values of a node are strictly increasing, the map
from its domain into the rationals is injective. Since ℚ is
countable, every node has countably many indices.

This does not mean that the set of all nodes of one length is
countable; that would be a different, much stronger statement.
-/

#check StrictMono.injective
#check Set.countable_of_injective_of_countable_image

theorem rationalNode_domain_countable (x : RationalNode) :
    Countable {i : Ordinal // i < x.length} := by
  have hinj : Function.Injective x.values :=
    x.increasing.injective
  have hinjOn : Set.InjOn x.values
      (Set.univ : Set {i : Ordinal // i < x.length}) := by
    intro i hi j hj heq
    exact hinj heq
  have himage :
      (x.values '' (Set.univ : Set {i : Ordinal // i < x.length})).Countable := by
    exact Set.to_countable _
  have hdomain :
      (Set.univ : Set {i : Ordinal // i < x.length}).Countable :=
    Set.countable_of_injective_of_countable_image hinjOn himage
  exact Set.countable_univ_iff.mp hdomain

/-!
No increasing rational sequence can have
an uncountable ordinal as its domain. I'm stating the result in terms
of countability of the index subtype, without yet proving a
separate characterization of the ordinal omega_1.
-/

theorem no_rationalNode_of_uncountable_length
    (β : Ordinal)
    (hβ : ¬ Countable {i : Ordinal // i < β}) :
    ¬ ∃ x : RationalNode, x.length = β := by
  rintro ⟨x, hx⟩
  have hcount := rationalNode_domain_countable x
  rw [hx] at hcount
  exact hβ hcount

/-!
## Bounded nodes
In the classical rational-sequence approach, it is useful to
keep the values of an individual node bounded above. The
boundedness condition is separate from strict monotonicity.
-/

def BoundedAbove (x : RationalNode) : Prop :=
  ∃ q : ℚ, ∀ i, x.values i < q

/-!
### Why an upper bound is not quite enough
For a limit-length increasing sequence, every entry can be less
than q even when the entries approach q as closely as possible.
Then there is no new rational strictly between all the old
entries and q. An extension construction needs some spare room.

For example, the rational values 1 - 1/(n+1), n in Nat, increase
towards 1. Every entry is below 1, but we cannot append another
entry below 1 that is larger than all the previous entries.

So I'm going to introduce a stronger property: an intermediate rational p
bounds every old entry, and p itself remains below q.
This is a proposed invariant for recursive level selection, not a
claim that all bounded nodes satisfy it for every q.
-/

def HasRoomBelow (x : RationalNode) (q : ℚ) : Prop :=
  ∃ p : ℚ, p < q ∧ ∀ i, x.values i < p

-- Easy check: a node with room below q is certainly bounded.
theorem boundedAbove_of_hasRoomBelow
    (x : RationalNode) (q : ℚ)
    (h : HasRoomBelow x q) : BoundedAbove x := by
  obtain ⟨p, hpq, hp⟩ := h
  exact ⟨p, hp⟩

def CandidateLevel (β : Ordinal) : Set RationalNode :=
  {x | x.length = β ∧ BoundedAbove x}

theorem candidateLevel_length
    (β : Ordinal) (x : RationalNode)
    (hx : x ∈ CandidateLevel β) : x.length = β := by
  exact hx.1

/-!
## Part II (Checkpoint 4): Restriction to an earlier ordinal
For a sequence x of length γ and β ≤ γ, we can take the
initial segment of x of length β. This gives us a way to talk
about ancestors without referring to a picture of a tree.
-/

def restrictNode (x : RationalNode) (β : Ordinal)
    (hβ : β ≤ x.length) : RationalNode where
  length := β
  values := fun i => x.values ⟨i.val, lt_of_lt_of_le i.property hβ⟩
  increasing := by
    intro i j hij
    apply x.increasing
    exact hij

theorem restrictNode_length
    (x : RationalNode) (β : Ordinal)
    (hβ : β ≤ x.length) :
    (restrictNode x β hβ).length = β := by
  rfl

theorem restrictNode_endExtends
    (x : RationalNode) (β : Ordinal)
    (hβ : β ≤ x.length) :
    EndExtends (restrictNode x β hβ) x := by
  refine ⟨hβ, ?_⟩
  intro i
  rfl

-- Boundedness survives when we throw away later entries.
theorem boundedAbove_restrictNode
    (x : RationalNode) (hx : BoundedAbove x)
    (β : Ordinal) (hβ : β ≤ x.length) :
    BoundedAbove (restrictNode x β hβ) := by
  obtain ⟨q, hq⟩ := hx
  refine ⟨q, ?_⟩
  intro i
  exact hq ⟨i.val, lt_of_lt_of_le i.property hβ⟩

/-!
## Comparable initial segments
This is the important tree-like fact for end-extension.
If both x and y are initial segments of z, then whichever has
the shorter length must be an initial segment of the other.

Compare this directly with predecessorsComparable from
Checkpoint 1: it is the defining local comparability feature
of a tree order.
-/

theorem initialSegments_comparable
    {x y z : RationalNode}
    (hxz : EndExtends x z) (hyz : EndExtends y z) :
    EndExtends x y ∨ EndExtends y x := by
  rcases le_total x.length y.length with hxy | hyx
  · left
    refine ⟨hxy, ?_⟩
    intro i
    calc
      x.values i =
          z.values ⟨i.val, lt_of_lt_of_le i.property hxz.1⟩ :=
            hxz.2 i
      _ = y.values
          ⟨i.val, lt_of_lt_of_le i.property hxy⟩ := by
            symm
            exact hyz.2 ⟨i.val, lt_of_lt_of_le i.property hxy⟩
  · right
    refine ⟨hyx, ?_⟩
    intro i
    calc
      y.values i =
          z.values ⟨i.val, lt_of_lt_of_le i.property hyz.1⟩ :=
            hyz.2 i
      _ = x.values
          ⟨i.val, lt_of_lt_of_le i.property hyx⟩ := by
            symm
            exact hxz.2 ⟨i.val, lt_of_lt_of_le i.property hyx⟩

/-!
## Selecting a subtree
We can't take every bounded increasing sequence at every
countable ordinal. Instead, the desired construction should
pick a smaller family closed under initial segments.

This structure records the properties a chosen family
would need. It does not assert that such a family of height
ω₁ has been constructed yet.
-/

structure PrefixClosedFamily where
  nodes : Set RationalNode
  bounded : ∀ x, x ∈ nodes → BoundedAbove x
  prefix_closed :
    ∀ (x : RationalNode), x ∈ nodes →
      ∀ (β : Ordinal) (hβ : β ≤ x.length),
        restrictNode x β hβ ∈ nodes

def familyLevel (F : PrefixClosedFamily) (β : Ordinal) :
    Set RationalNode :=
  {x | x ∈ F.nodes ∧ x.length = β}

-- Every initial segment of a chosen node also belongs to the family.
theorem familyLevel_nonempty_below_node
    (F : PrefixClosedFamily) (x : RationalNode)
    (hx : x ∈ F.nodes) (β : Ordinal)
    (hβ : β ≤ x.length) :
    (familyLevel F β).Nonempty := by
  refine ⟨restrictNode x β hβ, ?_⟩
  exact ⟨F.prefix_closed x hx β hβ, rfl⟩

-- A selected level is contained in the ambient candidate level.
theorem familyLevel_subset_candidateLevel
    (F : PrefixClosedFamily) (β : Ordinal) :
    familyLevel F β ⊆ CandidateLevel β := by
  intro x hx
  exact ⟨hx.2, F.bounded x hx.1⟩

/-!
## A specific obligation for the recursive construction
I really don't want to hide the difficult transfinite step under the name
"select a countable family". The classical construction maintains
an extension requirement: if x is already selected at level β and
there is room below a rational q, then at every later countable
level γ we can find an extension y while retaining room below q.

The condition below is a specification. Right now we haven't
built a family satisfying it. At a successor stage one can append
a rational. At a countable limit stage one needs a cofinal sequence
of earlier stages and a compatible chain of extensions.

The latter step is the actual mathematical problem to work on.
-/

def HasExtensionInvariant (F : PrefixClosedFamily) : Prop :=
  ∀ (β γ : Ordinal), β < γ → γ < Ordinal.omega 1 →
    ∀ (x : RationalNode), x ∈ familyLevel F β →
      ∀ q : ℚ, HasRoomBelow x q →
        ∃ y : RationalNode,
          y ∈ familyLevel F γ ∧
          EndExtends x y ∧ HasRoomBelow y q

/-!
## Stating the remaining Aronszajn conditions
These are predicates, rather than existence proofs.
We still need a specific family for which they hold.
-/

def HasCountableSelectedLevels (F : PrefixClosedFamily) : Prop :=
  ∀ β : Ordinal, (familyLevel F β).Countable

def HasHeightOmegaOneByLength (F : PrefixClosedFamily) : Prop :=
  (∀ x, x ∈ F.nodes → x.length < Ordinal.omega 1) ∧
  (∀ β : Ordinal, β < Ordinal.omega 1 →
    (familyLevel F β).Nonempty)

def IsEndExtensionChain (b : Set RationalNode) : Prop :=
  ∀ x, x ∈ b → ∀ y, y ∈ b →
    EndExtends x y ∨ EndExtends y x

def HasNoCofinalEndExtensionChain (F : PrefixClosedFamily) : Prop :=
  ¬ ∃ b : Set RationalNode,
      b ⊆ F.nodes ∧ IsEndExtensionChain b ∧
      (∀ β : Ordinal, β < Ordinal.omega 1 →
        ∃ x, x ∈ b ∧ β ≤ x.length)

def HasAronszajnConditions (F : PrefixClosedFamily) : Prop :=
  HasHeightOmegaOneByLength F ∧
  HasCountableSelectedLevels F ∧
  HasNoCofinalEndExtensionChain F

/-!
## A mathematical checkpoint
Assuming the proofs compile I've established the following:
* Increasing rational nodes have countable index types.
* End-extension is reflexive and transitive.
* Restrictions exist and are initial segments.
* Any two initial segments of the same node are comparable.
* Prefix closure gives earlier nonempty family levels.

What's NOT established here:
* EndExtends as a complete PartialOrder (antisymmetry remains).
* Ordinal rank equals a node's sequence length.
* Existence of a selected family with countable levels up to omega_1.
* The extension invariant at countable limit ordinals.
* Absence of cofinal branches for the selected family in Lean.

### A proof I want to work out
Claim: EndExtends is antisymmetric. On paper:
if x extends to y and y extends to x, their lengths are equal.
For every index in that common domain the values agree, hence
x and y are the same structure. Lean will require handling the
subtype domains carefully (proof irrelevance/extensionality).

I'll write a proof sketch by hand, then try Lean's
`ext` tactic and inspect its goals. This would let me turn the
end-extension relation into a real partial order rather than
only saying it behaves "like a tree".

### Next decisions
Given all selected levels below a countable limit ordinal γ:
1. Choose an increasing countable cofinal sequence γₙ → γ.
2. For each earlier selected node x and rational bound q with
   spare room, try to build a compatible sequence xₙ of extensions.
3. Explain why its union is still a strictly increasing rational
   sequence with room below q.
4. Explain why choosing one extension for each pair (x, q)
   yields countably many new nodes at level γ.
-/

end AronszajnTrees
