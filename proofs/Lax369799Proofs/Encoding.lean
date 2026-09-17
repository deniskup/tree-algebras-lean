import Lax369799.EncodingTheorems

namespace Lax369799Proofs.Encoding
open Lax369799.RankedSystems Lax369799.TransitionSystems
open Lax369799.TransitionEncoding

private noncomputable def encode {P : Type} (S : TransitionSystem P) :
    System (TransitionAlphabet P) 0 := by
  classical
  let W (v : S.Vertex) := {w : S.Vertex // S.edge v w}
  let e (v : S.Vertex) : W v ≃ Fin (Fintype.card (W v)) := Fintype.equivFin (W v)
  let G : Presentation (TransitionAlphabet P) 0 S.Vertex := {
    label := fun v => ⟨Fintype.card (W v), S.valuation v⟩
    initial := {S.initial}
    root := ∅
    edge := fun v d t => ∃ w : W v, d = (e v w).val ∧ t = .inl w.val
    direction_valid := by rintro v d t ⟨w, rfl, rfl⟩; exact (e v w).isLt }
  have step : ∀ v w, G.Step v w ↔ S.edge v w := by
    intro v w
    constructor
    · rintro ⟨d, u, hd, hu⟩
      have hwu : w = u.val := Sum.inl.inj hu
      exact hwu ▸ u.property
    · intro h
      exact ⟨(e v ⟨w, h⟩).val, ⟨w, h⟩, rfl, rfl⟩
  refine ⟨⟨S.size, G, ?_⟩, ?_⟩
  · intro v
    exact ⟨S.initial, Or.inl rfl,
      Relation.ReflTransGen.mono (fun v w h => (step v w).mpr h) _ _ (S.reachable v)⟩
  · refine ⟨⟨S.initial, rfl⟩, rfl, ?_⟩
    intro v d hd
    let w := (e v).symm ⟨d, hd⟩
    refine ⟨.inl w.val, ⟨w, ?_, rfl⟩, ?_⟩
    · simp [w]
    · rintro t ⟨u, hu, rfl⟩
      have h : e v u = (⟨d, hd⟩ : Fin (Fintype.card (W v))) := Fin.ext hu.symm
      have hw : u = w := (e v).injective (h.trans (by simp [w]))
      rw [hw]

/--
---
conclusion: Lax369799.EncodingTheorems.encoding_exists
---
Enumerate the successor set of each vertex to give its outgoing edges
directions. The vertex set, initial vertex, and valuations are retained.
-/
theorem encoding_exists {P : Type} (S : TransitionSystem P) :
    ∃ T : System (TransitionAlphabet P) 0, decode T = S := by
  classical
  refine ⟨encode S, ?_⟩
  have hi : (decode (encode S)).initial = S.initial := by
    have h := Classical.choose_spec (encode S).property.1
    change ({S.initial} : Set S.Vertex) = {Classical.choose (encode S).property.1} at h
    exact (Set.singleton_injective h).symm
  have he : (decode (encode S)).edge = S.edge := by
    funext v w
    apply propext
    change (∃ d, ∃ u : {w // S.edge v w},
      d = (Fintype.equivFin {w // S.edge v w} u).val ∧ Sum.inl w = Sum.inl u.val) ↔ _
    constructor
    · rintro ⟨d, u, hd, hu⟩
      exact (Sum.inl.inj hu) ▸ u.property
    · intro h
      exact ⟨_, ⟨w, h⟩, rfl, rfl⟩
  cases S
  unfold decode
  congr 1

end Lax369799Proofs.Encoding
