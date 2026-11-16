import Lax369799.InitialResolutionApproximation
import Lax369799Proofs.RootResolutionApproximation

set_option backward.isDefEq.respectTransparency false
namespace Lax369799Proofs.InitialResolutionApproximation
open Lax369799.RankedSystems Lax369799.Morphisms Lax369799.FiniteResolutionNormalForms
open Lax369799.ObservedSubstitution Lax369799.RootExpansion Lax369799.RootlessFlattening
open Lax369799Proofs.Pullbacks

private theorem remove_roots {A : RankedSet} {n : ℕ} {V : Type} [Fintype V]
    (G : Presentation A n V) (R : System A n) :
    InitYield (trim { G with root := ∅ }) R ↔ InitYield (trim G) R := by
  constructor
  · rintro ⟨D, ⟨f⟩, hu⟩
    let g := PresentationObservations.toPresentation f
    exact ⟨D, ⟨lift {g with root := fun _ h => False.elim (g.root _ h)}⟩, hu⟩
  · rintro ⟨D, ⟨f⟩, hu⟩
    let g := PresentationObservations.toPresentation f
    refine ⟨D, ⟨lift {g with root := ?_}⟩, hu⟩
    intro v hv
    rw [D.property.2.1] at hv
    exact False.elim hv

/--
---
conclusion: Lax369799.InitialResolutionApproximation.finite_support
---
Remove root marks, restrict the root-free substitution pattern, and
apply finite support to a direct-resolution witness. The same support
admits replacement labels, and covers restore the original observations.
-/
theorem finite_support {A : RankedSet} {n : ℕ} {V : Type} [Fintype V]
    (P : Presentation (SetSystem A) n V) (R : System A n)
    (hR : InitYield (trim (Lax369799.FinitePresentations.flattenPresentation (finiteLabels P))) R) :
    ∃ (m : ℕ) (v : Fin m → V) (c : ∀ i, Component (P.label (v i)).2),
      (∀ i, (c i).rooted = false) ∧
      ∀ (Q : ∀ v, SetSystem A (P.label v).1),
        (∀ i, DirectResolution (Q (v i)) (c i).system) →
        InitYield (trim (Lax369799.FinitePresentations.flattenPresentation
          (finiteLabels (replaceLabels P Q)))) R := by
  classical
  let X := RootProfileSubstitution.initialPattern P
  let PX := trimLabels X
  have hx : ∀ v, (PX.label v).2.graph.root = ∅ := by intro v; ext w; rfl
  have hr := (remove_roots _ R).mpr hR
  have hr := (YieldObservations.obs_cover (RootProfileSubstitution.initialCover P) R).mpr hr
  have hr := (YieldObservations.obs_cover (ObservedSubstitution.innerCover X) R).mpr hr
  have hr := (YieldObservations.obs_cover (ObservedSubstitution.outerCover PX hx) R).mpr hr
  obtain ⟨D, hd, f, hf⟩ := hr
  obtain ⟨k, d, hdroot, hs⟩ := FiniteResolutionApproximation.finite_support (trim PX) D hd
  let I := (u : (trim PX).Vertex) × Fin (k u)
  let e := Fintype.equivFin I
  let location := fun i : I => vertex PX i.1
  let c : (i : I) → Component (P.label (location i)).2 := fun i => {
    system := (d i.1 i.2).system
    rooted := false
    resolves := by
      apply (RootResolutionApproximation.direct_initial_part (P.label (location i)).2 _).mp
      have hh := (d i.1 i.2).resolves
      simp only [hdroot, Bool.false_eq_true, ↓reduceIte] at hh
      exact hh }
  refine ⟨Fintype.card I, fun j => location (e.symm j), fun j => c (e.symm j), fun _ => rfl, ?_⟩
  intro Q hQ
  let Y := RootProfileSubstitution.initialPattern (replaceLabels P Q)
  let PY := trimLabels Y
  have hy : ∀ v, (PY.label v).2.graph.root = ∅ := by intro v; ext w; rfl
  have hlocal (i : I) : DirectResolution
      (Lax369799.RootObservations.initialPart (Q (location i))) (d i.1 i.2).system := by
    apply (RootResolutionApproximation.direct_initial_part (Q (location i)) _).mpr
    have hh := hQ (e i)
    change DirectResolution (Q (location (e.symm (e i)))) (c (e.symm (e i))).system at hh
    rw [e.symm_apply_apply] at hh
    exact hh
  obtain ⟨U, hu, g, hg⟩ := hs (fun u => (PY.label (vertex PX u)).2) (fun u j => hlocal ⟨u, j⟩)
  have hur : InitYield (Lax369799.Flattening.flatten
      (Lax369799.ProfileSubstitution.withLabels (trim PX) (fun u => (PY.label (vertex PX u)).2))) R :=
    ⟨U, hu, MorphismTheorems.compose g f,
      MorphismTheorems.system_morphism_locally_surjective U R _⟩
  have hur := (YieldObservations.obs_cover (ObservedSubstitution.outerCover PY hy) R).mp hur
  have hur := (YieldObservations.obs_cover (ObservedSubstitution.innerCover Y) R).mp hur
  have hur := (YieldObservations.obs_cover (RootProfileSubstitution.initialCover (replaceLabels P Q)) R).mp hur
  exact (remove_roots _ R).mp hur

end Lax369799Proofs.InitialResolutionApproximation
