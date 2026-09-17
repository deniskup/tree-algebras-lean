import Lax369799.FiniteAcceptance
import Lax369799Proofs.FiniteSyntacticAlgebra
import Lax369799Proofs.Acceptance

namespace Lax369799Proofs.FiniteAcceptance
open Lax369799.RankedSystems (RankedSet Presentation)
open Lax369799.FinitePresentations Lax369799.FiniteContextualOrder Lax369799.FiniteAcceptance
open Lax369799Proofs.Pullbacks

private theorem trim_iso {A : RankedSet} {n : ℕ} {V W : Type} [Fintype V] [Fintype W]
    {G : Presentation A n V} {H : Presentation A n W} (f : PresentationIso G H) :
    Lax369799.Morphisms.UnfoldEquivalent (Lax369799.RankedSystems.trim G)
      (Lax369799.RankedSystems.trim H) := by
  let m := UntrimmedFlattening.isoMap f
  have hf : (trimMap m).LocallySurjective := by
    apply trimMap_surjective m
    · intro w hw
      obtain ⟨v, rfl⟩ := f.vertex.surjective w
      exact ⟨v, (f.initial v).mp hw, rfl⟩
    · intro w hw
      obtain ⟨v, rfl⟩ := f.vertex.surjective w
      exact ⟨v, (f.root v).mp hw, rfl⟩
    · intro v d t ht
      let s := Sum.map f.vertex.symm id t
      have he : Sum.map f.vertex id s = t := by cases t <;> simp [s]
      refine ⟨s, (f.edge v d s).mp ?_, he⟩
      rw [he]
      exact ht
  exact ⟨_, ⟨MorphismTheorems.identity _, MorphismTheorems.identity_surjective _⟩,
    ⟨trimMap m, hf⟩⟩

/--
---
conclusion: Lax369799.FiniteAcceptance.accepting_isomorphic
---
An isomorphism restricts to a locally surjective map on reachable parts.
Their yields, and hence their acceptance tests, coincide.
-/
theorem accepting_isomorphic {A : RankedSet} (L : Lax369799.Algebras.Language A) :
    IsoInvariant (Accepting L) := by
  intro S T h
  obtain ⟨f⟩ := h
  exact Acceptance.accepting_unfold L _ _ (trim_iso f)

/--
---
conclusion: Lax369799.FiniteAcceptance.syntactic_substitution_algebra
---
Apply the contextual quotient construction to yield acceptance. This
establishes substitution evaluation, without asserting yield continuity.
-/
theorem syntactic_substitution_algebra {A : RankedSet} (L : Lax369799.Algebras.Language A) :
    ∃ E : Lax369799.FiniteSyntacticAlgebra.Algebra (Carrier (Accepting L)),
      ∀ n (S : FiniteSystem (FiniteSystem A) n),
        E.eval n (relabel (quotientMap (Accepting L)) S) =
          quotientMap (Accepting L) n (flatten S) :=
  FiniteSyntacticAlgebra.contextual_algebra (Accepting L) (accepting_isomorphic L)

end Lax369799Proofs.FiniteAcceptance
