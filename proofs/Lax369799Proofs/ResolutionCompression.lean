import Lax369799.ResolutionCompression
import Lax369799Proofs.Renaming
import Lax369799Proofs.Yields

set_option backward.isDefEq.respectTransparency false

namespace Lax369799Proofs.ResolutionCompression
open Lax369799.RankedSystems Lax369799.Resolutions Lax369799.Renaming
open Lax369799.ResolutionCompression Lax369799Proofs.Pullbacks

noncomputable def compressedSystem {A : RankedSet} {n : ℕ} (T : System (System A) n)
    (arity : T.val.Vertex → ℕ)
    (τ : ∀ v, Fin (T.val.graph.label v).1 → Fin (arity v))
    (sectionMap : ∀ v, Fin (arity v) → Fin (T.val.graph.label v).1) :
    System (System A) n := by
  let G := compressedPresentation T arity τ sectionMap
  refine ⟨trim G, ?_⟩
  obtain ⟨v, hv⟩ := T.property.1
  apply Yields.trim_deterministic G v hv T.property.2.1
  intro w d hd
  obtain ⟨t, ht, hu⟩ := T.property.2.2 w (sectionMap w ⟨d, hd⟩).val (sectionMap w ⟨d, hd⟩).isLt
  refine ⟨t, ⟨⟨d, hd⟩, rfl, ht⟩, ?_⟩
  rintro u ⟨i, hi, hh⟩
  have he : i = ⟨d, hd⟩ := Fin.ext hi.symm
  subst i
  exact hu u hh

noncomputable def compressedResolution {A : RankedSet} {n : ℕ} (S : SetSystem (SetSystem A) n)
    (T : System (System A) n) (r : FlattenResolution S T)
    (arity : T.val.Vertex → ℕ)
    (τ : ∀ v, Fin (T.val.graph.label v).1 → Fin (arity v))
    (sectionMap : ∀ v, Fin (arity v) → Fin (T.val.graph.label v).1)
    (hσ : ∀ v i, r.variableMap v (sectionMap v (τ v i)) = r.variableMap v i) :
    FlattenResolution S (compressedSystem T arity τ sectionMap) where
  vertex := fun v => r.vertex (vertex (compressedPresentation T arity τ sectionMap) (by exact v))
  variableMap := fun v i => r.variableMap
    (vertex (compressedPresentation T arity τ sectionMap) (by exact v))
    (sectionMap (vertex (compressedPresentation T arity τ sectionMap) (by exact v)) (by exact i))
  initial := by intro v hv; exact r.initial _ hv
  resolves := by
    intro v
    let w := vertex (compressedPresentation T arity τ sectionMap) (by exact v)
    exact Renaming.resolution_factor (Lax369799.Flattening.Inner S (r.vertex w))
      (T.val.graph.label w).2 (r.variableMap w) (τ w) (r.variableMap w ∘ sectionMap w)
      (hσ w) (r.resolves w)
  transition := by
    intro v i w h
    let v' := vertex (compressedPresentation T arity τ sectionMap) (by exact v)
    let w' := vertex (compressedPresentation T arity τ sectionMap) (by exact w)
    obtain ⟨j, he, hj⟩ := h
    have he : j = (show Fin (arity v') from i) := Fin.ext he.symm
    subst j
    exact r.transition v' (sectionMap v' i) w' hj
  exit := by
    intro v i j h
    let v' := vertex (compressedPresentation T arity τ sectionMap) (by exact v)
    obtain ⟨a, he, ha⟩ := h
    have he : a = (show Fin (arity v') from i) := Fin.ext he.symm
    subst a
    exact r.exit v' (sectionMap v' i) j ha

/--
---
conclusion: Lax369799.ResolutionCompression.compress_flatten_resolution
---
Choose the indicated outer successors and trim to reachable vertices.
Renaming composition preserves the local resolution morphisms; the old
outer resolution preserves the selected transitions and exits.
-/
theorem compress_flatten_resolution {A : RankedSet} {n : ℕ} (S : SetSystem (SetSystem A) n)
    (T : System (System A) n) (r : FlattenResolution S T)
    (arity : T.val.Vertex → ℕ)
    (τ : ∀ v, Fin (T.val.graph.label v).1 → Fin (arity v))
    (sectionMap : ∀ v, Fin (arity v) → Fin (T.val.graph.label v).1)
    (hσ : ∀ v i, r.variableMap v (sectionMap v (τ v i)) = r.variableMap v i)
    (bound : ℕ) (hb : ∀ v j, Nat.card {i // r.variableMap v (sectionMap v i) = j} ≤ bound) :
    ∃ U : System (System A) n,
      U.val = trim (compressedPresentation T arity τ sectionMap) ∧
      ∃ r' : FlattenResolution S U,
        ∀ v j, Nat.card {i // r'.variableMap v i = j} ≤ bound := by
  refine ⟨compressedSystem T arity τ sectionMap, rfl,
    compressedResolution S T r arity τ sectionMap hσ, ?_⟩
  intro v j
  exact hb (vertex (compressedPresentation T arity τ sectionMap) (by exact v)) (by exact j)

end Lax369799Proofs.ResolutionCompression
