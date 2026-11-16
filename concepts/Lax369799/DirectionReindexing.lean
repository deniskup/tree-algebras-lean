import Lax369799.TransitionEncoding

/-!
---
title: Reindexing the outgoing directions at each vertex
type: theorem
---
Replace the directions at every vertex by a finite set mapping
surjectively onto the original directions. Successors and valuations
are preserved after forgetting direction order and multiplicity. The
resulting deterministic system has an isomorphic decoding, as used in
the cloning and rerouting constructions of Lemma 108.
-/

namespace Lax369799.DirectionReindexing
open RankedSystems TransitionEncoding

structure Reindexing {P : Type} (S : System (TransitionAlphabet P) 0) where
  arity : S.val.Vertex → ℕ
  map : ∀ v, Fin (arity v) → Fin (S.val.graph.label v).1
  surjective : ∀ v, Function.Surjective (map v)

def graph {P : Type} (S : System (TransitionAlphabet P) 0) (R : Reindexing S) :
    Presentation (TransitionAlphabet P) 0 S.val.Vertex where
  label := fun v => ⟨R.arity v, (S.val.graph.label v).2⟩
  initial := S.val.graph.initial
  root := ∅
  edge := fun v d t => ∃ i : Fin (R.arity v), d = i.val ∧ S.val.graph.edge v (R.map v i).val t
  direction_valid := by rintro v d t ⟨i, rfl, _⟩; exact i.isLt

structure Realizes {P : Type} (S : System (TransitionAlphabet P) 0) (R : Reindexing S)
    (T : System (TransitionAlphabet P) 0) where
  vertex : T.val.Vertex ≃ S.val.Vertex
  label : ∀ v, T.val.graph.label v = ⟨R.arity (vertex v), (S.val.graph.label (vertex v)).2⟩
  initial : ∀ v, T.val.graph.initial v ↔ S.val.graph.initial (vertex v)
  edge : ∀ v d t, T.val.graph.edge v d t ↔
    ∃ i : Fin (R.arity (vertex v)), d = i.val ∧
      S.val.graph.edge (vertex v) (R.map (vertex v) i).val (Sum.map vertex id t)

/-- Canonical realization, retaining exactly the original vertex type. -/
def system {P : Type} (S : System (TransitionAlphabet P) 0) (R : Reindexing S) :
    System (TransitionAlphabet P) 0 := by
  let G := graph S R
  have hstep {v w : S.val.Vertex} (h : S.val.graph.Step v w) : G.Step v w := by
    obtain ⟨d, hd⟩ := h
    let i : Fin (S.val.graph.label v).1 := ⟨d, S.val.graph.direction_valid _ _ _ hd⟩
    obtain ⟨j, hj⟩ := R.surjective v i
    exact ⟨j.val, j, rfl, by simpa only [hj] using hd⟩
  have hreach (v : S.val.Vertex) : G.Reachable v := by
    obtain ⟨a, ha, hp⟩ := S.val.reachable v
    have hi : S.val.graph.initial a := ha.elim id (fun h => by rw [S.property.2.1] at h; exact h.elim)
    refine ⟨a, Or.inl hi, ?_⟩
    induction hp with
    | refl => exact .refl
    | @tail y z hp hyz ih => exact ih.tail (hstep hyz)
  let U : SetSystem (TransitionAlphabet P) 0 := ⟨S.val.size, G, hreach⟩
  have hdet : U.Deterministic := by
    refine ⟨S.property.1, rfl, ?_⟩
    intro v d hd
    let i : Fin (R.arity v) := ⟨d, hd⟩
    obtain ⟨t, ht, hu⟩ := S.property.2.2 v (R.map v i).val (R.map v i).isLt
    refine ⟨t, ⟨i, rfl, ht⟩, ?_⟩
    rintro t' ⟨j, hj, ht'⟩
    have hji : j = i := Fin.ext hj.symm
    subst j
    exact hu t' ht'
  exact ⟨U, hdet⟩

/-- Its realization map is the identity on vertices. -/
def realizes {P : Type} (S : System (TransitionAlphabet P) 0) (R : Reindexing S) :
    Realizes S R (system S R) where
  vertex := Equiv.refl _
  label := fun _ => rfl
  initial := fun _ => Iff.rfl
  edge := by intro v d t; cases t <;> exact Iff.rfl


axiom zero_iff {P : Type} (S : System (TransitionAlphabet P) 0) (R : Reindexing S)
    (v : S.val.Vertex) : R.arity v = 0 ↔ (S.val.graph.label v).1 = 0

axiom realization {P : Type} (S : System (TransitionAlphabet P) 0) (R : Reindexing S) :
    ∃ T, Nonempty (Realizes S R T)

axiom decode_isomorphic {P : Type} {S T : System (TransitionAlphabet P) 0}
    (R : Reindexing S) (h : Realizes S R T) : Isomorphic (decode T) (decode S)

end Lax369799.DirectionReindexing
