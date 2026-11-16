import Lax369799.RootResolutionApproximation
import Lax369799Proofs.FiniteResolutionApproximation
import Lax369799Proofs.YieldObservations

set_option backward.isDefEq.respectTransparency false
namespace Lax369799Proofs.RootResolutionApproximation
open Lax369799.RankedSystems Lax369799.Morphisms Lax369799.FiniteResolutionNormalForms
open Lax369799.ObservedSubstitution Lax369799.RootExpansion Lax369799.RootlessFlattening
open Lax369799Proofs.Pullbacks

theorem direct_initial_part {A : RankedSet} {n : ℕ} (S : SetSystem A n) (R : System A n) :
    DirectResolution (Lax369799.RootObservations.initialPart S) R ↔ DirectResolution S R := by
  constructor
  · rintro ⟨f⟩
    exact ⟨MorphismTheorems.compose f (RootObservations.inclusion S)⟩
  · rintro ⟨f⟩
    refine ⟨lift ?_⟩
    exact {
      toFun := f.toFun
      initial := f.initial
      root := by intro v hv; rw [R.property.2.1] at hv; exact False.elim hv
      label := f.label
      edge := f.edge }

private theorem part_resolution {A : RankedSet} {n : ℕ} (S : SetSystem A n)
    (b : Bool) (R : System A n) :
    DirectResolution (trim (component (Lax369799.FinitePresentations.ofSetSystem S) b).graph) R ↔
      DirectResolution (if b then uproot S else S) R := by
  cases b with
  | false => exact direct_initial_part S R
  | true => rfl

/--
---
conclusion: Lax369799.RootResolutionApproximation.finite_support
---
Pass to the root-entry expansion, restrict its root-free labels, and
factor an initial resolution. Its finite support records the entry flag
at each used label. The same support admits the replacement expansion.
-/
theorem finite_support {A : RankedSet} {n : ℕ} {V : Type} [Fintype V]
    (P : Presentation (SetSystem A) n V) (R : System A n)
    (hR : InitYield (trim (startAtRoots
      (Lax369799.FinitePresentations.flattenPresentation (finiteLabels P)))) R) :
    ∃ (m : ℕ) (v : Fin m → V) (c : ∀ i, Component (P.label (v i)).2),
      ∀ (Q : ∀ v, SetSystem A (P.label v).1),
        (∀ i, DirectResolution (if (c i).rooted then uproot (Q (v i)) else Q (v i)) (c i).system) →
        InitYield (trim (startAtRoots
          (Lax369799.FinitePresentations.flattenPresentation (finiteLabels (replaceLabels P Q))))) R := by
  classical
  let X := pattern (finiteLabels P)
  let PX := trimLabels X
  have hx : ∀ v, (PX.label v).2.graph.root = ∅ := by intro v; ext w; rfl
  have hr := (YieldObservations.obs_cover (RootExpansion.expansionCover (finiteLabels P)) R).mpr hR
  have hr := (YieldObservations.obs_cover (ObservedSubstitution.innerCover X) R).mpr hr
  have hr := (YieldObservations.obs_cover (ObservedSubstitution.outerCover PX hx) R).mpr hr
  obtain ⟨D, hd, ⟨f, hf⟩⟩ := hr
  obtain ⟨k, d, hdroot, hs⟩ := FiniteResolutionApproximation.finite_support (trim PX) D hd
  let I := (u : (trim PX).Vertex) × Fin (k u)
  let e := Fintype.equivFin I
  let location := fun i : I => vertex PX i.1
  let c : (i : I) → Component (P.label (location i).2).2 := fun i => {
    system := (d i.1 i.2).system
    rooted := (location i).1
    resolves := by
      apply (part_resolution (P.label (location i).2).2 (location i).1 _).mp
      have hh := (d i.1 i.2).resolves
      simp only [hdroot, Bool.false_eq_true, ↓reduceIte] at hh
      exact hh }
  refine ⟨Fintype.card I, fun j => (location (e.symm j)).2, fun j => c (e.symm j), ?_⟩
  intro Q hQ
  let Y := pattern (finiteLabels (replaceLabels P Q))
  let PY := trimLabels Y
  have hy : ∀ v, (PY.label v).2.graph.root = ∅ := by intro v; ext w; rfl
  have hlocal (i : I) : DirectResolution
      (trim (component (Lax369799.FinitePresentations.ofSetSystem (Q (location i).2)) (location i).1).graph)
      (d i.1 i.2).system := by
    apply (part_resolution (Q (location i).2) (location i).1 _).mpr
    have hh := hQ (e i)
    change DirectResolution (if (c (e.symm (e i))).rooted then
      uproot (Q (location (e.symm (e i))).2) else Q (location (e.symm (e i))).2)
      (c (e.symm (e i))).system at hh
    rw [e.symm_apply_apply] at hh
    exact hh
  obtain ⟨U, hu, g, hg⟩ := hs (fun u => (PY.label (vertex PX u)).2) (fun u j => hlocal ⟨u, j⟩)
  have hur : InitYield (Lax369799.Flattening.flatten
      (Lax369799.ProfileSubstitution.withLabels (trim PX) (fun u => (PY.label (vertex PX u)).2))) R :=
    ⟨U, hu, MorphismTheorems.compose g f,
      MorphismTheorems.system_morphism_locally_surjective U R _⟩
  have hur := (YieldObservations.obs_cover (ObservedSubstitution.outerCover PY hy) R).mp hur
  have hur := (YieldObservations.obs_cover (ObservedSubstitution.innerCover Y) R).mp hur
  exact (YieldObservations.obs_cover (RootExpansion.expansionCover (finiteLabels (replaceLabels P Q))) R).mp hur

end Lax369799Proofs.RootResolutionApproximation
