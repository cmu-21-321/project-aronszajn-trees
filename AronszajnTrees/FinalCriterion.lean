import AronszajnTrees.LevelConstruction
import AronszajnTrees.NoCofinalBranch

/-!
# Aronszajn Trees — A Conditional Final Construction Criterion
Now we're collecting the properties that a selected rational-sequence
family must satisfy in order to meet our Aronszajn conditions.

The ambient tree has no cofinal branch (NoCofinalBranch), while the
extension invariant and a root guarantee that all countable levels
are populated (LevelConstruction). Thus the real existence problem
reduces to constructing a suitable family with countable selected
levels and a working extension invariant.
-/

namespace AronszajnTrees

/-!
## Putting the established implications together
A candidate family has the Aronszajn properties if:
1. Every selected node has countable ordinal length.
2. Every selected level is countable.
3. The zero-th level contains a node with room below some rational.
4. The extension invariant holds across all later countable stages.

Under these assumptions, the height and no-cofinal-branch conditions
follow from our earlier lemmas.
-/

theorem aronszajn_of_extension_invariant
    (F : PrefixClosedFamily)
    (hshort : ∀ x : RationalNode,
      x ∈ F.nodes → x.length < Ordinal.omega 1)
    (hcount : HasCountableSelectedLevels F)
    (hroot : ∃ x : RationalNode,
      x ∈ familyLevel F 0 ∧ ∃ q : ℚ, HasRoomBelow x q)
    (hext : HasExtensionInvariant F) :
    HasAronszajnConditions F := by
  have hheight : HasHeightOmegaOneByLength F := by
    constructor
    · exact hshort
    · exact nonempty_levels_of_extension_invariant F hroot hext
  exact aronszajn_of_height_and_countable_levels F hheight hcount

/-!
## What still prevents an unconditional existence theorem
The hypotheses hcount and hext are NOT automatically satisfied by
any arbitrary PrefixClosedFamily! We have given a working successor
extension construction, but we haven't shown how to choose the
selected nodes consistently at every countable limit ordinal.

The final existence statement would assert that there exists F
satisfying the four assumptions of the theorem above. It is not
proved here, and should not be presented as though it were.
-/

end AronszajnTrees
