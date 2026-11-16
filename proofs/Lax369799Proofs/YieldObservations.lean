import Lax369799Proofs.YieldSubstitution
import Lax369799Proofs.RootProfileSubstitution
import Lax369799Proofs.PlantAcceptance

set_option backward.isDefEq.respectTransparency false
namespace Lax369799Proofs.YieldObservations
open Lax369799.RankedSystems Lax369799.Morphisms Lax369799.PresentationCovers
open Lax369799.RootExpansion Lax369799.ObservedSubstitution Lax369799.RootlessFlattening
open Lax369799Proofs.Pullbacks

private abbrev Obs {A : RankedSet} {n : ℕ} {V : Type} [Fintype V]
    (G : Presentation A n V) (U : System A n) := InitYield (trim G) U

private theorem obs_map {A : RankedSet} {n : ℕ} {V : Type} [Fintype V]
    (G : Presentation A n V) (U : System A n) :
    Obs G U ↔ ∃ D : System A n, Nonempty (Map D.val.graph G) ∧ UnfoldsTo U.val D.val := by
  constructor
  · rintro ⟨D, ⟨d⟩, hd⟩
    exact ⟨D, ⟨PresentationObservations.toPresentation d⟩, hd⟩
  · rintro ⟨D, ⟨d⟩, hd⟩
    exact ⟨D, ⟨lift d⟩, hd⟩

theorem obs_cover {A : RankedSet} {n : ℕ} {V W : Type} [Fintype V] [Fintype W]
    {G : Presentation A n V} {H : Presentation A n W} (f : Cover G H) (U : System A n) :
    Obs G U ↔ Obs H U := by
  let g : Map G H := ⟨f.toFun, f.initial, f.root, f.label, f.edge⟩
  exact ⟨Yields.initial_yield_forward (trimMap g),
    Yields.initial_yield_backward (trimMap g)
      (trimMap_surjective g f.initial_lift f.root_lift f.edge_lift)⟩

private theorem obs_remove_roots {A : RankedSet} {n : ℕ} {V : Type} [Fintype V]
    (G : Presentation A n V) (U : System A n) :
    Obs { G with root := ∅ } U ↔ Obs G U := by
  rw [obs_map, obs_map]
  constructor
  · rintro ⟨D, ⟨d⟩, hd⟩
    exact ⟨D, ⟨{d with root := fun v hv => False.elim (d.root v hv)}⟩, hd⟩
  · rintro ⟨D, ⟨d⟩, hd⟩
    refine ⟨D, ⟨{d with root := ?_}⟩, hd⟩
    intro v hv
    rw [D.property.2.1] at hv
    exact False.elim hv

private theorem initial_part {A : RankedSet} {n : ℕ} (S : SetSystem A n) (U : System A n) :
    InitYield (Lax369799.RootObservations.initialPart S) U ↔ InitYield S U := by
  constructor
  · exact Yields.initial_yield_forward (RootObservations.inclusion S)
  · rintro ⟨D, ⟨d⟩, hd⟩
    refine ⟨D, ⟨lift ?_⟩, hd⟩
    exact {
      toFun := d.toFun
      initial := d.initial
      root := by intro v hv; rw [D.property.2.1] at hv; exact False.elim hv
      label := d.label
      edge := d.edge }

private theorem root_mono {A : RankedSet} {n : ℕ} {S T : SetSystem A n}
    (h : YieldBelow S T) (U : System A n) (hu : InitYield (uproot S) U) :
    InitYield (uproot T) U := by
  rcases h (plant U.val) (Or.inr ⟨U, hu, rfl⟩) with ⟨V, _, he⟩ | ⟨V, hv, he⟩
  · exact False.elim (PlantAcceptance.system_ne_plant V U he.symm)
  · exact (PlantAcceptance.plant_injective U V he).symm ▸ hv

private theorem transfer_rootless {A : RankedSet} {n : ℕ} {V : Type} [Fintype V]
    (P : Presentation (SetSystem A) n V) (Q : ∀ v, SetSystem A (P.label v).1)
    (hP : ∀ v, (P.label v).2.graph.root = ∅) (hQ : ∀ v, (Q v).graph.root = ∅)
    (h : ∀ v U, InitYield (P.label v).2 U → InitYield (Q v) U) (U : System A n) :
    Obs (Lax369799.FinitePresentations.flattenPresentation (finiteLabels P)) U →
      Obs (Lax369799.FinitePresentations.flattenPresentation (finiteLabels (replaceLabels P Q))) U := by
  intro hu
  have hu := (obs_cover (ObservedSubstitution.outerCover P hP) U).mpr hu
  obtain ⟨R, hr, ⟨r, _⟩⟩ := hu
  obtain ⟨W, hw, ⟨w, _⟩⟩ := YieldSubstitution.transfer_initial_resolution (trim P)
    (fun v => Q (vertex P v)) (fun v => h (vertex P v)) R hr
  apply (obs_cover (ObservedSubstitution.outerCover (replaceLabels P Q) hQ) U).mp
  exact ⟨W, hw, ⟨MorphismTheorems.compose w r,
    MorphismTheorems.system_morphism_locally_surjective W U _⟩⟩

theorem transfer_initial {A : RankedSet} {n : ℕ} {V : Type} [Fintype V]
    (P : Presentation (SetSystem A) n V) (Q : ∀ v, SetSystem A (P.label v).1)
    (h : ∀ v U, InitYield (P.label v).2 U → InitYield (Q v) U) (U : System A n) :
    Obs (Lax369799.FinitePresentations.flattenPresentation (finiteLabels P)) U →
      Obs (Lax369799.FinitePresentations.flattenPresentation (finiteLabels (replaceLabels P Q))) U := by
  let X := RootProfileSubstitution.initialPattern P
  let Y := RootProfileSubstitution.initialPattern (replaceLabels P Q)
  let PX := trimLabels X
  let PY := trimLabels Y
  have hx : ∀ v, (PX.label v).2.graph.root = ∅ := by intro v; ext w; rfl
  have hy : ∀ v, (PY.label v).2.graph.root = ∅ := by intro v; ext w; rfl
  have hp : ∀ v R, InitYield (PX.label v).2 R → InitYield (PY.label v).2 R := by
    intro v R hr
    exact (initial_part (Q v) R).mpr (h v R ((initial_part (P.label v).2 R).mp hr))
  intro hu
  have hu := (obs_remove_roots _ U).mpr hu
  have hu := (obs_cover (RootProfileSubstitution.initialCover P) U).mpr hu
  have hu := (obs_cover (ObservedSubstitution.innerCover X) U).mpr hu
  have hu := transfer_rootless PX (fun v => (PY.label v).2) hx hy hp U hu
  have hu := (obs_cover (ObservedSubstitution.innerCover Y) U).mp hu
  have hu := (obs_cover (RootProfileSubstitution.initialCover (replaceLabels P Q)) U).mp hu
  exact (obs_remove_roots _ U).mp hu

theorem transfer_root {A : RankedSet} {n : ℕ} {V : Type} [Fintype V]
    (P : Presentation (SetSystem A) n V) (Q : ∀ v, SetSystem A (P.label v).1)
    (h : ∀ v, YieldBelow (P.label v).2 (Q v)) (U : System A n) :
    Obs (startAtRoots (Lax369799.FinitePresentations.flattenPresentation (finiteLabels P))) U →
      Obs (startAtRoots (Lax369799.FinitePresentations.flattenPresentation
        (finiteLabels (replaceLabels P Q)))) U := by
  let X := pattern (finiteLabels P)
  let Y := pattern (finiteLabels (replaceLabels P Q))
  let PX := trimLabels X
  let PY := trimLabels Y
  have hx : ∀ v, (PX.label v).2.graph.root = ∅ := by intro v; ext w; rfl
  have hy : ∀ v, (PY.label v).2.graph.root = ∅ := by intro v; ext w; rfl
  have hp : ∀ v R, InitYield (PX.label v).2 R → InitYield (PY.label v).2 R := by
    rintro ⟨b, v⟩ R hr
    cases b with
    | false =>
      exact (initial_part (Q v) R).mpr
        (ResolutionLifting.initial_mono (h v) R ((initial_part (P.label v).2 R).mp hr))
    | true => exact root_mono (h v) R hr
  intro hu
  have hu := (obs_cover (RootExpansion.expansionCover (finiteLabels P)) U).mpr hu
  have hu := (obs_cover (ObservedSubstitution.innerCover X) U).mpr hu
  have hu := transfer_rootless PX (fun v => (PY.label v).2) hx hy hp U hu
  have hu := (obs_cover (ObservedSubstitution.innerCover Y) U).mp hu
  exact (obs_cover (RootExpansion.expansionCover (finiteLabels (replaceLabels P Q))) U).mp hu

/--
---
conclusion: Lax369799.YieldSubstitution.flatten_mono
---
Transfer initial resolutions through variable-splitting resolutions.
For root yields, expand root entries into starting copies and use covers
to relate their initial resolutions to the original root resolutions.
-/
theorem flatten_mono {A : RankedSet} {n : ℕ}
    (P : SetSystem (SetSystem A) n) (Q : ∀ v, SetSystem A (P.graph.label v).1)
    (hQ : ∀ v, YieldBelow (Lax369799.Flattening.Inner P v) (Q v)) :
    YieldBelow (Lax369799.Flattening.flatten P)
      (Lax369799.Flattening.flatten (Lax369799.ProfileSubstitution.withLabels P Q)) := by
  intro W hw
  rcases hw with ⟨U, hu, rfl⟩ | ⟨U, hu, rfl⟩
  · exact Or.inl ⟨U, transfer_initial P.graph Q
      (fun v => ResolutionLifting.initial_mono (hQ v)) U hu, rfl⟩
  · let G := Lax369799.FinitePresentations.flattenPresentation (finiteLabels P.graph)
    let H := Lax369799.FinitePresentations.flattenPresentation (finiteLabels (replaceLabels P.graph Q))
    have hG := obs_cover (PresentationObservations.rootedCover (FiniteAcceptance.trimProjection G)) U
    have hH := obs_cover (PresentationObservations.rootedCover (FiniteAcceptance.trimProjection H)) U
    exact Or.inr ⟨U, hH.mpr (transfer_root P.graph Q hQ U (hG.mp hu)), rfl⟩

/--
---
conclusion: Lax369799.FlatteningTheorems.yield_context_congruence
---
View the context as an outer pattern. Its ordinary letters have unchanged
atomic labels, and its hole has the given yield inclusion. Apply monotonicity
of flattening, including both initial and root yields.
-/
theorem yield_context_congruence {A : RankedSet} {k n : ℕ}
    (C : Lax369799.Flattening.SetContext A k n) (S T : SetSystem A k) (h : YieldBelow S T) :
    YieldBelow (Lax369799.Flattening.plug C S) (Lax369799.Flattening.plug C T) := by
  have hh : ∀ r a, YieldBelow (Lax369799.Flattening.substitution S r a)
      (Lax369799.Flattening.substitution T r a) := by
    intro r a
    cases a with
    | inl a => exact fun _ hy => hy
    | inr hkr =>
      obtain ⟨hkr⟩ := hkr
      subst r
      exact h
  exact flatten_mono (relabel (Lax369799.Flattening.substitution S) C.system)
    (fun v => Lax369799.Flattening.substitution T _ (C.system.graph.label v).2)
    (fun v => hh _ (C.system.graph.label v).2)

end Lax369799Proofs.YieldObservations
