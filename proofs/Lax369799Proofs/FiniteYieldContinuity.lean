import Lax369799.FiniteYieldContinuity
import Lax369799Proofs.YieldContinuity
import Lax369799Proofs.InitialResolutionApproximation

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
namespace Lax369799Proofs.FiniteYieldContinuity
open Lax369799.RankedSystems Lax369799.Morphisms Lax369799.FiniteResolutionNormalForms
open Lax369799.ObservedSubstitution Lax369799.FiniteYieldContinuity
open Lax369799Proofs.Pullbacks

private def pattern {A : RankedSet} {k n : ℕ}
    (C : Lax369799.FiniteContexts.Context A k n) (S : SetSystem A k) :
    Presentation (SetSystem A) n C.system.Vertex := {
  C.system.graph with label := fun v => ⟨(C.system.graph.label v).1,
    Lax369799.Flattening.substitution S _ (C.system.graph.label v).2⟩ }

private theorem pattern_eq {A : RankedSet} {k n : ℕ}
    (C : Lax369799.FiniteContexts.Context A k n) (S : SetSystem A k) :
    finiteLabels (pattern C S) =
      (Lax369799.FinitePresentations.relabel
        (Lax369799.FiniteContexts.substitution (Lax369799.FinitePresentations.ofSetSystem S)) C.system).graph := by
  have hh : ∀ r a, Lax369799.FinitePresentations.ofSetSystem (Lax369799.Flattening.substitution S r a) =
      Lax369799.FiniteContexts.substitution (Lax369799.FinitePresentations.ofSetSystem S) r a := by
    intro r a
    cases a with
    | inl a => rfl
    | inr h => obtain ⟨h⟩ := h; subst r; rfl
  unfold finiteLabels pattern Lax369799.FinitePresentations.relabel
  congr 1
  funext v
  exact congrArg (Sigma.mk _) (hh _ _)

private theorem cover_yields {A : RankedSet} {n : ℕ} {V W : Type} [Fintype V] [Fintype W]
    {G : Presentation A n V} {H : Presentation A n W} (f : Lax369799.PresentationCovers.Cover G H) :
    YieldEquivalent (trim G) (trim H) := by
  let g : Map G H := ⟨f.toFun, f.initial, f.root, f.label, f.edge⟩
  exact (Yields.morphism_yields (trimMap g)).2
    (trimMap_surjective g f.initial_lift f.root_lift f.edge_lift)

private theorem insert_observation {A : RankedSet} {k n : ℕ}
    (C : Lax369799.FiniteContexts.Context A k n) (S : SetSystem A k) :
    YieldEquivalent (insert C S)
      (trim (Lax369799.FinitePresentations.flattenPresentation (finiteLabels (pattern C S)))) := by
  rw [pattern_eq]
  exact cover_yields (FiniteCovers.isoCover (UntrimmedFlattening.isoSymm
    (UntrimmedFlattening.reindexIso _ (Fintype.equivFin _))))

private theorem presentation_mono {A : RankedSet} {n : ℕ} {V : Type} [Fintype V]
    (P : Presentation (SetSystem A) n V) (Q : ∀ v, SetSystem A (P.label v).1)
    (hQ : ∀ v, YieldBelow (P.label v).2 (Q v)) :
    YieldBelow (trim (Lax369799.FinitePresentations.flattenPresentation (finiteLabels P)))
      (trim (Lax369799.FinitePresentations.flattenPresentation (finiteLabels (replaceLabels P Q)))) := by
  intro W hw
  rcases hw with ⟨U, hu, rfl⟩ | ⟨U, hu, rfl⟩
  · exact Or.inl ⟨U, YieldObservations.transfer_initial P Q
      (fun v => ResolutionLifting.initial_mono (hQ v)) U hu, rfl⟩
  · let G := Lax369799.FinitePresentations.flattenPresentation (finiteLabels P)
    let H := Lax369799.FinitePresentations.flattenPresentation (finiteLabels (replaceLabels P Q))
    have hG := YieldObservations.obs_cover (PresentationObservations.rootedCover (FiniteAcceptance.trimProjection G)) U
    have hH := YieldObservations.obs_cover (PresentationObservations.rootedCover (FiniteAcceptance.trimProjection H)) U
    exact Or.inr ⟨U, hH.mpr (YieldObservations.transfer_root P Q hQ U (hG.mp hu)), rfl⟩

/--
---
conclusion: Lax369799.FiniteYieldContinuity.context_mono
---
Transfer observations through the unpruned substitution presentation,
then use its enumeration cover to recover the plugged finite context.
-/
theorem context_mono {A : RankedSet} {k n : ℕ}
    (C : Lax369799.FiniteContexts.Context A k n) (S T : SetSystem A k) (h : YieldBelow S T) :
    YieldBelow (insert C S) (insert C T) := by
  have hh : ∀ r a, YieldBelow (Lax369799.Flattening.substitution S r a)
      (Lax369799.Flattening.substitution T r a) := by
    intro r a
    cases a with
    | inl a => exact fun _ h => h
    | inr he => obtain ⟨he⟩ := he; subst r; exact h
  intro R hr
  apply (insert_observation C T R).mpr
  exact presentation_mono (pattern C S)
    (fun v => Lax369799.Flattening.substitution T _ (C.system.graph.label v).2)
    (fun v => hh _ _) R ((insert_observation C S R).mp hr)

private theorem hole_support {A : RankedSet} {k n m : ℕ}
    (C : Lax369799.FiniteContexts.Context A k n) (S : SetSystem A k)
    (v : Fin m → C.system.Vertex) (c : ∀ i, Component ((pattern C S).label (v i)).2) :
    ∃ (l : ℕ) (ds : Fin l → Component S), ∀ i,
      DirectResolution
        (if (c i).rooted then uproot (Lax369799.Flattening.substitution (trim (family ds).graph) _ (C.system.graph.label (v i)).2)
         else Lax369799.Flattening.substitution (trim (family ds).graph) _ (C.system.graph.label (v i)).2) (c i).system := by
  classical
  let I := {i : Fin m // Lax369799.Flattening.IsHole (C.system.graph.label (v i))}
  let e := Fintype.equivFin I
  have hchoice (i : I) := ContextResolutionApproximation.hole_component S
    (C.system.graph.label (v i.val)).2 i.property (c i.val)
  let d := fun i : I => Classical.choose (hchoice i)
  have hd (i : I) := Classical.choose_spec (hchoice i)
  let ds := fun j => d (e.symm j)
  let Q := trim (family ds).graph
  refine ⟨Fintype.card I, ds, ?_⟩
  intro i
  by_cases hi : Lax369799.Flattening.IsHole (C.system.graph.label (v i))
  · apply (hd ⟨i, hi⟩ Q).mpr
    have hh := FiniteResolutionNormalForms.injectionResolution ds (e ⟨i, hi⟩)
    change DirectResolution (if (d (e.symm (e ⟨i, hi⟩))).rooted then uproot Q else Q)
      (d (e.symm (e ⟨i, hi⟩))).system at hh
    rw [e.symm_apply_apply] at hh
    exact hh
  · rw [ContextResolutionApproximation.substitution_nonhole S Q _ hi]
    exact (c i).resolves

private theorem resolution_approximation {A : RankedSet} {k n : ℕ}
    (C : Lax369799.FiniteContexts.Context A k n) (S : SetSystem A k) (R : SetSystem A n)
    (hr : Yield (insert C S) R) :
    ∃ (m : ℕ) (c : Fin m → Component S), Yield (insert C (trim (family c).graph)) R := by
  have hr := (insert_observation C S R).mp hr
  rcases hr with ⟨U, hu, rfl⟩ | ⟨U, hu, rfl⟩
  · obtain ⟨m, v, c, hc, hs⟩ := InitialResolutionApproximation.finite_support (pattern C S) U hu
    obtain ⟨l, ds, hd⟩ := hole_support C S v c
    let Q := trim (family ds).graph
    have hlocal : ∀ i, DirectResolution
        (Lax369799.Flattening.substitution Q _ (C.system.graph.label (v i)).2) (c i).system := by
      intro i
      have h := hd i
      simp only [hc, Bool.false_eq_true, ↓reduceIte] at h
      exact h
    have hu := hs (fun w => Lax369799.Flattening.substitution Q _ (C.system.graph.label w).2) hlocal
    refine ⟨l, ds, (insert_observation C Q U.val).mpr ?_⟩
    exact Or.inl ⟨U, hu, rfl⟩
  · let G := Lax369799.FinitePresentations.flattenPresentation (finiteLabels (pattern C S))
    have hu := (YieldObservations.obs_cover
      (PresentationObservations.rootedCover (FiniteAcceptance.trimProjection G)) U).mp hu
    obtain ⟨m, v, c, hs⟩ := RootResolutionApproximation.finite_support (pattern C S) U hu
    obtain ⟨l, ds, hd⟩ := hole_support C S v c
    let Q := trim (family ds).graph
    have hu := hs (fun w => Lax369799.Flattening.substitution Q _ (C.system.graph.label w).2) hd
    let H := Lax369799.FinitePresentations.flattenPresentation (finiteLabels (pattern C Q))
    refine ⟨l, ds, (insert_observation C Q (plant U.val)).mpr (Or.inr ⟨U, ?_, rfl⟩)⟩
    exact (YieldObservations.obs_cover
      (PresentationObservations.rootedCover (FiniteAcceptance.trimProjection H)) U).mpr hu

/--
---
conclusion: Lax369799.FiniteYieldContinuity.continuity
---
Finite support at ordinary and root entries supplies direct-resolution
families. Covers replace these by arbitrary yields; their morphisms to
the original label and context monotonicity give the converse.
-/
theorem continuity {A : RankedSet} {k n : ℕ}
    (C : Lax369799.FiniteContexts.Context A k n) (S : SetSystem A k) (R : SetSystem A n) :
    Yield (insert C S) R ↔
      ∃ (m : ℕ) (F : Fin m → SetSystem A k),
        (∀ i, Yield S (F i)) ∧ Yield (insert C (Lax369799.YieldContinuity.finiteSum F)) R := by
  classical
  constructor
  · intro hr
    obtain ⟨m, c, hc⟩ := resolution_approximation C S R hr
    let F := fun i => YieldContinuity.value (c i).system (c i).rooted
    have he := YieldContinuity.family_equivalent c F (fun i => YieldContinuity.valueCover (c i).system (c i).rooted)
    exact ⟨m, F, fun i => YieldContinuity.component_yield (c i),
      context_mono C _ _ (fun U h => (he U).mp h) R hc⟩
  · rintro ⟨m, F, hF, hr⟩
    let c := fun i => Classical.choose (YieldContinuity.witness (hF i))
    let f := fun i => Classical.choice (Classical.choose_spec (YieldContinuity.witness (hF i)))
    have he := YieldContinuity.family_equivalent c F f
    have hr := context_mono C _ _ (fun U h => (he U).mpr h) R hr
    exact context_mono C _ _ (Yields.morphism_yields
      (project (FiniteResolutionNormalForms.familyMap c))).1 R hr

end Lax369799Proofs.FiniteYieldContinuity
