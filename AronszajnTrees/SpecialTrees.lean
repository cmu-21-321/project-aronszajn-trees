import AronszajnTrees.ResearchNotes
import AronszajnTrees.ConstructionOrder

/-!
# Aronszajn Trees — Special Trees and the Suslin Comparison
We tried introducing a coloring of a selected tree by natural
numbers, with different colors on distinct comparable nodes. And we
also defined a Suslin-like condition: every antichain is countable.

Here I want to prove two relationships rather than simply list them:
1. A countable antichain coloring makes every chain countable.
2. If every antichain is countable AND the family has such a
   coloring, then the entire family is countable.

Consequently, an uncountable special tree cannot be Suslin.
This is a conditional result. It does not construct a special
Aronszajn tree or a Suslin tree.
-/

namespace AronszajnTrees

/-!
## 1. A coloring is injective along chains
If b is a chain of selected nodes, then two distinct elements
of b are comparable. The coloring must give them distinct
natural numbers. Thus b injects into Nat and is countable.
-/

theorem chain_countable_of_antichain_coloring
    (F : PrefixClosedFamily)
    (hcolor : HasAntichainColoring F)
    (b : Set RationalNode)
    (hsub : b ⊆ F.nodes)
    (hchain : IsEndExtensionChain b) : b.Countable := by
  obtain ⟨color, hc⟩ := hcolor
  have hinj : Set.InjOn color b := by
    intro x hx y hy heq
    by_contra hne
    rcases hchain x hx y hy with hxy | hyx
    · exact (hc x y (hsub hx) (hsub hy) hne hxy) heq
    · exact (hc y x (hsub hy) (hsub hx) (Ne.symm hne) hyx) heq.symm
  have himage : (color '' b).Countable := Set.to_countable _
  exact Set.countable_of_injective_of_countable_image hinj himage

/-!
## 2. A Suslin-style antichain condition and a coloring
For each natural number n, the fiber of the coloring is an
antichain (proved in ResearchNotes). If F has only countable
antichains, each fiber is countable. Since F.nodes is covered
by countably many such fibers, F.nodes is itself countable.
-/

theorem family_countable_of_coloring_and_countable_antichains
    (F : PrefixClosedFamily)
    (hcolor : HasAntichainColoring F)
    (hanti : HasOnlyCountableAntichains F) :
    F.nodes.Countable := by
  obtain ⟨color, hc⟩ := hcolor
  have hfiber : ∀ n : ℕ,
      ({x : RationalNode | x ∈ F.nodes ∧ color x = n} :
        Set RationalNode).Countable := by
    intro n
    apply hanti
    · intro x hx
      exact hx.1
    · exact coloring_fiber_antichain F color hc n
  have hcount :
      (⋃ n : ℕ, {x : RationalNode | x ∈ F.nodes ∧ color x = n}).Countable :=
    Set.countable_iUnion hfiber
  apply hcount.mono
  intro x hx
  apply Set.mem_iUnion.mpr
  exact ⟨color x, ⟨hx, rfl⟩⟩

/-!
## 3. Why a special uncountable tree cannot be Suslin
An uncountable family cannot simultaneously have a countable
antichain coloring and only countable antichains.

The hypothesis that F.nodes is uncountable is explicit here.
To specialize this to an Aronszajn tree of height ω₁, we still
need to connect height ω₁ to uncountability of the node set.
-/

theorem uncountable_special_not_suslin
    (F : PrefixClosedFamily)
    (hcolor : HasAntichainColoring F)
    (huncount : ¬ F.nodes.Countable) :
    ¬ HasSuslinLikeConditions F := by
  intro hsuslin
  apply huncount
  exact family_countable_of_coloring_and_countable_antichains
    F hcolor hsuslin.2

end AronszajnTrees
