import Lax369799.FiniteAcceptance
import Lax369799Proofs.FiniteSyntacticAlgebra
import Lax369799Proofs.SumYields

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

noncomputable def trimProjection {A : RankedSet} {n : ℕ} {V : Type} [Fintype V]
    (G : Presentation A n V) :
    Lax369799.PresentationCovers.Cover (Lax369799.RankedSystems.trim G).graph G where
  toFun := vertex G
  label := fun _ => rfl
  initial := fun _ h => h
  root := fun _ h => h
  edge := fun _ _ _ h => h
  initial_lift := by
    intro v hv
    have hr : G.Reachable v := ⟨v, Or.inl hv, .refl⟩
    refine ⟨index G ⟨v, hr⟩, ?_, vertex_index G v hr⟩
    change G.initial (vertex G (index G ⟨v, hr⟩))
    rw [vertex_index]
    exact hv
  root_lift := by
    intro v hv
    have hr : G.Reachable v := ⟨v, Or.inr hv, .refl⟩
    refine ⟨index G ⟨v, hr⟩, ?_, vertex_index G v hr⟩
    change G.root (vertex G (index G ⟨v, hr⟩))
    rw [vertex_index]
    exact hv
  edge_lift := by
    intro v d t ht
    cases t with
    | inl w =>
      have hw : G.Reachable w := by
        obtain ⟨r, hr, hp⟩ := ((index G).symm v).property
        exact ⟨r, hr, hp.tail ⟨d, ht⟩⟩
      refine ⟨.inl (index G ⟨w, hw⟩), ?_, ?_⟩
      · change G.edge (vertex G v) d (.inl (vertex G (index G ⟨w, hw⟩)))
        rw [vertex_index]
        exact ht
      · exact congrArg Sum.inl (vertex_index G w hw)
    | inr i => exact ⟨.inr i, ht, rfl⟩

private theorem sumPresentation_eq {A : RankedSet} {n : ℕ} {V W : Type}
    (G : Presentation A n V) (H : Presentation A n W) :
    sumPresentation G H = SumCovers.combine G H := by
  rfl

/--
---
conclusion: Lax369799.FiniteAcceptance.accepting_sum
---
The reachable restriction of a disjoint union has the same yields as the
disjoint union of the reachable restrictions. Apply the yield-union law.
-/
theorem accepting_sum {A : RankedSet} (L : Lax369799.Algebras.Language A)
    (S T : FiniteSystem A 0) : Accepting L (sum S T) ↔ Accepting L S ∧ Accepting L T := by
  classical
  let G := sumPresentation S.graph T.graph
  have he := (Acceptance.accepting_unfold L _ _
    (trim_iso (UntrimmedFlattening.reindexIso G (Fintype.equivFin _)))).symm
  change Accepting L (sum S T) ↔ Lax369799.SyntacticOrder.Accepting L
    (Lax369799.RankedSystems.trim G) at he
  obtain ⟨c, hc⟩ := SumCovers.trim_cover
    (SumCovers.combineCover (trimProjection S.graph) (trimProjection T.graph))
  have hs := Acceptance.accepting_unfold L _ _
    ⟨_, ⟨MorphismTheorems.identity _, MorphismTheorems.identity_surjective _⟩, ⟨c, hc⟩⟩
  rw [← SumCovers.sum_eq_trim] at hs
  have hg : G = SumCovers.combine S.graph T.graph := sumPresentation_eq _ _
  rw [hg] at he
  exact he.trans (hs.symm.trans (SumYields.accepting_sum L _ _))

/--
---
conclusion: Lax369799.FiniteAcceptance.accepting_system
---
Restricting an already reachable system preserves its unfolding class.
Acceptance of that system is membership in the original language.
-/
theorem accepting_system {A : RankedSet} (L : Lax369799.Algebras.Language A)
    (hL : Lax369799.Algebras.UnfoldInvariantLanguage L) (S : Lax369799.RankedSystems.System A 0) :
    Accepting L (ofSetSystem S.val) ↔ S ∈ L := by
  let f : Map S.val.graph S.val.graph := {
    toFun := id
    initial := fun _ h => h
    root := fun _ h => h
    label := fun _ => rfl
    edge := by intro v d t h; cases t <;> exact h }
  have hf : (project f).LocallySurjective := project_surjective f
    (fun v h => ⟨v, h, rfl⟩) (fun v h => ⟨v, h, rfl⟩)
    (fun v d t h => ⟨t, h, by cases t <;> rfl⟩)
  exact (Acceptance.accepting_unfold L _ _
    ⟨_, ⟨MorphismTheorems.identity _, MorphismTheorems.identity_surjective _⟩, ⟨project f, hf⟩⟩).trans
    (Acceptance.accepting_system L hL S)

/--
---
conclusion: Lax369799.FiniteAcceptance.accepting_empty
---
The empty presentation has no initial or root yields, so its universal
acceptance test holds for every language.
-/
theorem accepting_empty {A : RankedSet} (L : Lax369799.Algebras.Language A) :
    Accepting L (empty A 0) := by
  intro T ht
  rcases ht with ⟨U, ⟨D, ⟨d⟩, _⟩, _⟩ | ⟨U, ⟨D, ⟨d⟩, _⟩, _⟩
  · obtain ⟨v, _⟩ := D.property.1
    exact Fin.elim0 (vertex (empty A 0).graph (d.toFun v))
  · obtain ⟨v, _⟩ := D.property.1
    let G := (Lax369799.RankedSystems.trim (empty A 0).graph).graph
    exact Fin.elim0 (vertex (empty A 0).graph
      (vertex { G with initial := G.root, root := ∅ } (d.toFun v)))

end Lax369799Proofs.FiniteAcceptance
