import Lax369799Proofs.Flattening
import Lax369799Proofs.PresentationCovers

namespace Lax369799Proofs.AtomicFlattening
open Lax369799.RankedSystems Lax369799.Morphisms Lax369799.Flattening
open Lax369799.PresentationCovers

/--
---
conclusion: Lax369799.FlatteningTheorems.atomic_flatten_cover
---
Project each atomic component to its outer vertex. Atomic components have
one initial vertex and send each direction to the corresponding variable,
so this projection preserves and lifts every mark and edge.
-/
theorem atomic_flatten_cover {A : RankedSet} {n : ℕ} (S : SetSystem A n) :
    UnfoldsTo S (flatten (relabel (fun _ a => atomic a) S)) := by
  let R := relabel (fun _ a => atomic a) S
  let raw : Cover (Lax369799Proofs.Flattening.graph R) S.graph := {
    toFun := Sigma.fst
    label := fun _ => rfl
    initial := fun _ h => h.1
    root := fun _ h => h.elim False.elim And.left
    edge := by
      intro v d t ht
      rcases ht with ⟨w, ⟨i, _, he⟩, _⟩ | ⟨i, ⟨j, hd, he⟩, ht⟩
      · cases he
      · have hij : i = j := Sum.inr.inj he
        subst j
        subst d
        rcases ht with ⟨w, hw, _, rfl⟩ | ⟨j, hj, rfl⟩
        · exact hw
        · exact hj
    initial_lift := fun v hv => ⟨⟨v, (0 : Fin 1)⟩, ⟨hv, True.intro⟩, rfl⟩
    root_lift := fun v hv => ⟨⟨v, (0 : Fin 1)⟩, Or.inr ⟨hv, True.intro⟩, rfl⟩
    edge_lift := by
      intro v d t ht
      let i : Fin (S.graph.label v.1).1 := ⟨d, S.graph.direction_valid v.1 d t ht⟩
      cases t with
      | inl w => exact ⟨.inl ⟨w, (0 : Fin 1)⟩,
          Or.inr ⟨i, ⟨i, rfl, rfl⟩, Or.inl ⟨⟨w, (0 : Fin 1)⟩, ht, True.intro, rfl⟩⟩, rfl⟩
      | inr j => exact ⟨.inr j,
          Or.inr ⟨i, ⟨i, rfl, rfl⟩, Or.inr ⟨j, ht, rfl⟩⟩, rfl⟩ }
  exact Lax369799Proofs.trim_cover _ S raw

end Lax369799Proofs.AtomicFlattening
