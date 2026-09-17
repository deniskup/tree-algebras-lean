import Lax369799.RootObservations
import Lax369799Proofs.Renaming
import Lax369799Proofs.Yields
import Lax369799Proofs.FiniteOuterMorphisms

namespace Lax369799Proofs.RootObservations
open Lax369799.RankedSystems Lax369799.Morphisms Lax369799.Resolutions
open Lax369799.RootObservations Lax369799Proofs.Pullbacks

noncomputable def inclusion {A : RankedSet} {n : ℕ} (S : SetSystem A n) :
    Morphism (initialPart S) S := project {
  toFun := id
  initial := fun _ h => h
  root := fun _ h => False.elim h
  label := fun _ => rfl
  edge := fun _ _ t h => by simpa only [Sum.map_id_id, id_eq] using h }

/--
---
conclusion: Lax369799.RootObservations.resolution_initial_part
---
A deterministic resolution has no roots. Its morphism therefore factors
through the presentation with root marks removed and, by reachability,
through its initial restriction. The reverse direction uses inclusion.
-/
theorem resolution_initial_part {A : RankedSet} {m n : ℕ} (S : SetSystem A n)
    (T : System A m) (σ : Fin m → Fin n) :
    IsResolution (initialPart S) T σ ↔ IsResolution S T σ := by
  constructor
  · rintro ⟨f⟩
    exact ⟨MorphismTheorems.compose f (inclusion S)⟩
  · rintro ⟨f⟩
    let g : Map (rename σ T.val).graph { S.graph with root := ∅ } := {
      toFun := f.toFun
      initial := f.initial
      root := by
        intro v hv
        change v ∈ T.val.graph.root at hv
        rw [T.property.2.1] at hv
        exact False.elim hv
      label := f.label
      edge := f.edge }
    exact ⟨lift g⟩

/--
---
conclusion: Lax369799.RootObservations.initial_profile
---
Initial restriction preserves every resolution with its variable map and
observed value, hence preserves the whole initial profile.
-/
theorem initial_profile {A B : RankedSet} (ρ : ∀ n, System A n → B n) {n : ℕ}
    (S : SetSystem A n) : Profile ρ (initialPart S) = Profile ρ S := by
  ext e
  constructor
  · rintro ⟨T, hT, he⟩
    exact ⟨T, (resolution_initial_part S T e.2.2).mp hT, he⟩
  · rintro ⟨T, hT, he⟩
    exact ⟨T, (resolution_initial_part S T e.2.2).mpr hT, he⟩

/--
---
conclusion: Lax369799.RootObservations.rootless_outer_cover
---
Initial marks and edges lift through the outer cover. Roots of a flattened
presentation can only come from outer roots when every inner root set is
empty, so no global surjectivity on outer vertices is needed.
-/
theorem rootless_outer_cover {A : RankedSet} {n : ℕ}
    (S T : Lax369799.FinitePresentations.FiniteSystem (Lax369799.FinitePresentations.FiniteSystem A) n)
    (f : Lax369799.PresentationCovers.Cover S.graph T.graph)
    (h : ∀ w, (Lax369799.FinitePresentations.Inner T.graph w).graph.root = ∅) :
    Nonempty (Lax369799.PresentationCovers.Cover (Lax369799.FinitePresentations.flatten S).graph
      (Lax369799.FinitePresentations.flatten T).graph) :=
  ⟨FiniteOuterMorphisms.flattenCoverRootless f h⟩

end Lax369799Proofs.RootObservations
