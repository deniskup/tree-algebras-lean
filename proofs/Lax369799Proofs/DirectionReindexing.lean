import Lax369799.DirectionReindexing

namespace Lax369799Proofs.DirectionReindexing
open Lax369799.RankedSystems Lax369799.TransitionEncoding Lax369799.DirectionReindexing

/--
---
conclusion: Lax369799.DirectionReindexing.zero_iff
---
A surjection onto a nonempty set has a nonempty domain. A function into
an empty set has an empty domain.
-/
theorem zero_iff {P : Type} (S : System (TransitionAlphabet P) 0) (R : Reindexing S)
    (v : S.val.Vertex) : R.arity v = 0 ↔ (S.val.graph.label v).1 = 0 := by
  constructor
  · intro h
    by_contra hn
    obtain ⟨i, _⟩ := R.surjective v (⟨0, Nat.pos_of_ne_zero hn⟩ : Fin (S.val.graph.label v).1)
    have := i.isLt
    omega
  · intro h
    by_contra hn
    have i := R.map v (⟨0, Nat.pos_of_ne_zero hn⟩ : Fin (R.arity v))
    have := i.isLt
    omega

/--
---
conclusion: Lax369799.DirectionReindexing.realization
---
Keep the vertices, valuations and initial mark. Surjectivity lifts old
paths, and uniqueness of successors preserves determinism.
-/
theorem realization {P : Type} (S : System (TransitionAlphabet P) 0) (R : Reindexing S) :
    ∃ T, Nonempty (Realizes S R T) := ⟨system S R, ⟨realizes S R⟩⟩

/--
---
conclusion: Lax369799.DirectionReindexing.decode_isomorphic
---
The vertex equivalence preserves the unique initial vertex and every
valuation. The direction map and its surjectivity give the two directions
of preservation of the decoded edge relation.
-/
theorem decode_isomorphic {P : Type} {S T : System (TransitionAlphabet P) 0}
    (R : Reindexing S) (h : Realizes S R T) : Isomorphic (decode T) (decode S) := by
  refine ⟨h.vertex, ?_, ?_, ?_⟩
  · have hiT : T.val.graph.initial (decode T).initial := by
      change T.val.graph.initial (Classical.choose T.property.1)
      exact Eq.mpr (congrArg (fun M : Set T.val.Vertex =>
        (Classical.choose T.property.1) ∈ M) (Classical.choose_spec T.property.1)) rfl
    have hiS := (h.initial _).mp hiT
    rwa [Classical.choose_spec S.property.1] at hiS
  · intro v
    have hv := congrArg (fun s : Symbol (TransitionAlphabet P) => (s.2 : Set P)) (h.label v)
    exact hv
  · intro v w
    constructor
    · rintro ⟨d, hd⟩
      obtain ⟨i, _, hi⟩ := (h.edge v d (.inl w)).mp hd
      exact ⟨(R.map (h.vertex v) i).val, hi⟩
    · rintro ⟨d, hd⟩
      let i : Fin (S.val.graph.label (h.vertex v)).1 :=
        ⟨d, S.val.graph.direction_valid _ _ _ hd⟩
      obtain ⟨j, hj⟩ := R.surjective (h.vertex v) i
      refine ⟨j.val, (h.edge v j.val (.inl w)).mpr ⟨j, rfl, ?_⟩⟩
      change S.val.graph.edge (h.vertex v) (R.map (h.vertex v) j).val (.inl (h.vertex w))
      rw [hj]
      exact hd

end Lax369799Proofs.DirectionReindexing
