import Lax369799.PresentationObservations
import Lax369799Proofs.ProfileSubstitution
import Lax369799Proofs.FiniteAcceptance

namespace Lax369799Proofs.PresentationObservations
open Lax369799.RankedSystems Lax369799.Morphisms Lax369799.Algebras
open Lax369799.PresentationObservations Lax369799.PresentationCovers
open Lax369799Proofs.Pullbacks

noncomputable def toPresentation {A : RankedSet} {n : ℕ} {V : Type} [Fintype V]
    {S : SetSystem A n} {G : Presentation A n V} (r : Morphism S (trim G)) : Map S.graph G where
  toFun := fun v => vertex G (r.toFun v)
  initial := fun v hv => r.initial v hv
  root := fun v hv => r.root v hv
  label := r.label
  edge := by
    intro v d t ht
    have he := r.edge v d t ht
    cases t <;> exact he

theorem values_iff_map {A B : RankedSet} (E : Algebra B) (η : RankedMap A B)
    {n : ℕ} {V : Type} [Fintype V] (G : Presentation A n V) (b : B n) :
    b ∈ values E η G ↔ ∃ R : System A n, Nonempty (Map R.val.graph G) ∧
      E.eval n (relabelSystem η R) = b := by
  constructor
  · rintro ⟨R, ⟨r⟩, hb⟩
    exact ⟨R, ⟨toPresentation r⟩, hb⟩
  · rintro ⟨R, ⟨r⟩, hb⟩
    exact ⟨R, ⟨lift r⟩, hb⟩

/--
---
conclusion: Lax369799.PresentationObservations.values_remove_roots
---
Resolution domains have no roots, so their maps impose no condition on the
root marks of the target. Reachability is recovered by lifting each map.
-/
theorem values_remove_roots {A B : RankedSet} (E : Algebra B) (η : RankedMap A B)
    {n : ℕ} {V : Type} [Fintype V] (G : Presentation A n V) :
    values E η { G with root := ∅ } = values E η G := by
  ext b
  rw [values_iff_map, values_iff_map]
  constructor
  · rintro ⟨R, ⟨r⟩, hb⟩
    exact ⟨R, ⟨{ r with root := fun v hv => False.elim (r.root v hv) }⟩, hb⟩
  · rintro ⟨R, ⟨r⟩, hb⟩
    refine ⟨R, ⟨{ r with root := ?_ }⟩, hb⟩
    intro v hv
    rw [R.property.2.1] at hv
    exact False.elim hv

/--
---
conclusion: Lax369799.PresentationObservations.values_cover
---
Compose resolutions with the cover in one direction. In the other direction,
lift a resolution through the reachable cover by the pullback construction.
The lifted system has the same unfolding and hence the same value.
-/
theorem values_cover {A B : RankedSet} (E : Algebra B) (hE : UnfoldInvariant E)
    (η : RankedMap A B) {n : ℕ} {V W : Type} [Fintype V] [Fintype W]
    {G : Presentation A n V} {H : Presentation A n W} (f : Cover G H) :
    values E η G = values E η H := by
  let g : Map G H := ⟨f.toFun, f.initial, f.root, f.label, f.edge⟩
  let c := trimMap g
  have hc : c.LocallySurjective := trimMap_surjective g f.initial_lift f.root_lift f.edge_lift
  ext b
  constructor
  · rintro ⟨R, ⟨r⟩, hb⟩
    exact ⟨R, ⟨MorphismTheorems.compose r c⟩, hb⟩
  · rintro ⟨R, ⟨r⟩, hb⟩
    obtain ⟨S, hs, ⟨s, _⟩⟩ := Yields.lift_resolution c hc R r
    exact ⟨S, hs, (ProfileSubstitution.value_morphism E hE η S R s).trans hb⟩

def rootedCover {A : RankedSet} {n : ℕ} {V W : Type}
    {G : Presentation A n V} {H : Presentation A n W} (f : Cover G H) :
    Cover (Lax369799.RootExpansion.startAtRoots G) (Lax369799.RootExpansion.startAtRoots H) where
  toFun := f.toFun
  label := f.label
  initial := f.root
  root := fun _ h => False.elim h
  edge := f.edge
  initial_lift := f.root_lift
  root_lift := fun _ h => False.elim h
  edge_lift := f.edge_lift

/--
---
conclusion: Lax369799.PresentationObservations.root_values_cover
---
A cover remains a cover after replacing initial marks by root marks and
removing root marks. Apply preservation of initial resolution values.
-/
theorem root_values_cover {A B : RankedSet} (E : Algebra B) (hE : UnfoldInvariant E)
    (η : RankedMap A B) {n : ℕ} {V W : Type} [Fintype V] [Fintype W]
    {G : Presentation A n V} {H : Presentation A n W} (f : Cover G H) :
    values E η (Lax369799.RootExpansion.startAtRoots G) =
      values E η (Lax369799.RootExpansion.startAtRoots H) :=
  values_cover E hE η (rootedCover f)

end Lax369799Proofs.PresentationObservations
