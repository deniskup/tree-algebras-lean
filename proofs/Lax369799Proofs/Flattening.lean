import Lax369799.FlatteningTheorems
import Lax369799Proofs.Yields

namespace Lax369799Proofs.Flattening
open Lax369799.RankedSystems Lax369799.Morphisms Lax369799.Flattening

noncomputable def graph {A : RankedSet} {n : ℕ}
    (S : SetSystem (SetSystem A) n) :
    Presentation A n ((v : S.Vertex) × (Inner S v).Vertex) :=
  {
    label := fun v => (Inner S v.1).graph.label v.2
    initial := fun v => v.1 ∈ S.graph.initial ∧ v.2 ∈ (Inner S v.1).graph.initial
    root := fun v => v.2 ∈ (Inner S v.1).graph.root ∨
      (v.1 ∈ S.graph.root ∧ v.2 ∈ (Inner S v.1).graph.initial)
    edge := fun v d t =>
      (∃ w, (Inner S v.1).graph.edge v.2 d (.inl w) ∧ t = .inl ⟨v.1, w⟩) ∨
      (∃ i : Fin (S.graph.label v.1).1,
        (Inner S v.1).graph.edge v.2 d (.inr i) ∧
        ((∃ w : (v : S.Vertex) × (Inner S v).Vertex,
          S.graph.edge v.1 i.val (.inl w.1) ∧
          w.2 ∈ (Inner S w.1).graph.initial ∧ t = .inl w) ∨
         (∃ j, S.graph.edge v.1 i.val (.inr j) ∧ t = .inr j)))
    direction_valid := by
      intro v d t h
      rcases h with ⟨w, hw, _⟩ | ⟨i, hi, _⟩
      · exact (Inner S v.1).graph.direction_valid v.2 d _ hw
      · exact (Inner S v.1).graph.direction_valid v.2 d _ hi }

/--
---
conclusion: Lax369799.FlatteningTheorems.flatten_system
---
An inner edge either stays inside its component or exits through the
unique outer successor. In the latter case the next component has a
unique initial vertex. Restriction to reachable vertices preserves these
unique successors.
-/
theorem flatten_system {A : RankedSet} {n : ℕ} (S : System (System A) n) :
    ∃ T : System A n, SystemFlattening S T := by
  classical
  let R := relabel (fun _ (U : System A _) => U.val) S.val
  let G := graph R
  let initial (v : S.val.Vertex) := Classical.choose (S.val.graph.label v).2.property.1
  have initial_spec (v : S.val.Vertex) :
      (Inner R v).graph.initial = {initial v} :=
    Classical.choose_spec (S.val.graph.label v).2.property.1
  let outer (v : S.val.Vertex) (i : Fin (S.val.graph.label v).1) :=
    Classical.choose (S.property.2.2 v i.val i.isLt)
  have outer_edge (v : S.val.Vertex) (i : Fin (S.val.graph.label v).1) :
      S.val.graph.edge v i.val (outer v i) :=
    (Classical.choose_spec (S.property.2.2 v i.val i.isLt)).1
  have outer_unique (v : S.val.Vertex) (i : Fin (S.val.graph.label v).1)
      (t : S.val.Vertex ⊕ Fin n) (ht : S.val.graph.edge v i.val t) : t = outer v i :=
    (Classical.choose_spec (S.property.2.2 v i.val i.isLt)).2 t ht
  let next (v : S.val.Vertex) (t : (Inner R v).Vertex ⊕ Fin (S.val.graph.label v).1) :
      ((v : R.Vertex) × (Inner R v).Vertex) ⊕ Fin n :=
    match t with
    | .inl w => .inl ⟨v, w⟩
    | .inr i => match outer v i with
      | .inl w => .inl ⟨w, initial w⟩
      | .inr j => .inr j
  have edge_iff (v : (v : R.Vertex) × (Inner R v).Vertex) (d : ℕ) (t) :
      G.edge v d t ↔ ∃ s, (Inner R v.1).graph.edge v.2 d s ∧ t = next v.1 s := by
    constructor
    · rintro (⟨w, hw, rfl⟩ | ⟨i, hi, h⟩)
      · exact ⟨.inl w, hw, rfl⟩
      · refine ⟨.inr i, hi, ?_⟩
        rcases h with ⟨w, hw, hw', rfl⟩ | ⟨j, hj, rfl⟩
        · have he := outer_unique v.1 i (.inl w.1) hw
          have hin : w.2 = initial w.1 := by
            have h := hw'
            rw [initial_spec w.1] at h
            exact h
          simp only [next, ← he]
          exact congrArg Sum.inl (Sigma.ext rfl (heq_of_eq hin))
        · have he := outer_unique v.1 i (.inr j) hj
          simp only [next, ← he]
    · rintro ⟨s, hs, rfl⟩
      cases s with
      | inl w => exact Or.inl ⟨w, hs, rfl⟩
      | inr i =>
        refine Or.inr ⟨i, hs, ?_⟩
        cases ho : outer v.1 i with
        | inl w =>
          refine Or.inl ⟨⟨w, initial w⟩, ?_, ?_, ?_⟩
          · have h := outer_edge v.1 i
            rw [ho] at h; exact h
          · rw [initial_spec]; rfl
          · simp only [next, ho]
        | inr j =>
          refine Or.inr ⟨j, ?_, ?_⟩
          · have h := outer_edge v.1 i
            rw [ho] at h; exact h
          · simp only [next, ho]
  obtain ⟨i, hi⟩ := S.property.1
  have hdet : (trim G).Deterministic := by
    apply Lax369799Proofs.Yields.trim_deterministic G ⟨i, initial i⟩
    · ext v
      change (v.1 ∈ S.val.graph.initial ∧ v.2 ∈ (Inner R v.1).graph.initial) ↔ _
      rw [hi]
      constructor
      · rintro ⟨hv, hw⟩
        have hv : v.1 = i := hv
        rcases v with ⟨v, w⟩
        dsimp at hv
        subst v
        rw [initial_spec] at hw
        have hw : w = initial i := hw
        subst w
        rfl
      · rintro rfl
        exact ⟨rfl, by rw [initial_spec]; rfl⟩
    · ext v
      change ((v.2 ∈ (Inner R v.1).graph.root) ∨
        (v.1 ∈ S.val.graph.root ∧ v.2 ∈ (Inner R v.1).graph.initial)) ↔ False
      have hr : (Inner R v.1).graph.root = ∅ := (S.val.graph.label v.1).2.property.2.1
      rw [hr, S.property.2.1]
      exact ⟨fun h => h.elim (fun h => h) (fun h => h.1), False.elim⟩
    · intro v d hd
      obtain ⟨s, hs, hu⟩ := (S.val.graph.label v.1).2.property.2.2 v.2 d hd
      refine ⟨next v.1 s, (edge_iff v d _).mpr ⟨s, hs, rfl⟩, ?_⟩
      intro t ht
      obtain ⟨u, hu', he⟩ := (edge_iff v d t).mp ht
      rw [hu u hu'] at he
      exact he
  exact ⟨⟨trim G, hdet⟩, rfl⟩

/--
---
conclusion: Lax369799.FlatteningTheorems.flatten_resolution_sound
---
Pair the outer vertex map with the selected inner resolution maps.
Internal edges are preserved by inner resolutions; glued edges use the
outer transition and exit conditions with their variable maps.
-/
theorem flatten_resolution_sound {A : RankedSet} {n : ℕ}
    (S : SetSystem (SetSystem A) n) (T : System (System A) n)
    (h : Lax369799.Resolutions.FlattenResolution S T) (U : System A n)
    (hU : SystemFlattening T U) : DirectResolution (flatten S) U := by
  classical
  let R := relabel (fun _ (U : System A _) => U.val) T.val
  let inner (v : T.val.Vertex) := Classical.choice (h.resolves v)
  let f : Lax369799Proofs.Pullbacks.Map (graph R) (graph S) := {
    toFun := fun v => ⟨h.vertex v.1, (inner v.1).toFun v.2⟩
    initial := by
      intro v hv
      exact ⟨h.initial v.1 hv.1, (inner v.1).initial v.2 hv.2⟩
    root := by
      intro v hv
      rcases hv with hv | ⟨hv, _⟩
      · have hr := (T.val.graph.label v.1).2.property.2.1
        change v.2 ∈ (T.val.graph.label v.1).2.val.graph.root at hv
        rw [hr] at hv
        exact False.elim hv
      · change v.1 ∈ T.val.graph.root at hv
        rw [T.property.2.1] at hv
        exact False.elim hv
    label := fun v => (inner v.1).label v.2
    edge := by
      intro v d t ht
      rcases ht with ⟨w, hw, rfl⟩ | ⟨i, hi, ht⟩
      · have hh := (inner v.1).edge v.2 d (.inl w) ⟨.inl w, hw, rfl⟩
        exact Or.inl ⟨(inner v.1).toFun w, hh, rfl⟩
      · have hh := (inner v.1).edge v.2 d (.inr (h.variableMap v.1 i)) ⟨.inr i, hi, rfl⟩
        refine Or.inr ⟨h.variableMap v.1 i, hh, ?_⟩
        rcases ht with ⟨w, hw, hw', rfl⟩ | ⟨j, hj, rfl⟩
        · exact Or.inl ⟨⟨h.vertex w.1, (inner w.1).toFun w.2⟩,
            h.transition v.1 i w.1 hw, (inner w.1).initial w.2 hw', rfl⟩
        · exact Or.inr ⟨j, h.exit v.1 i j hj, rfl⟩ }
  have hf : Nonempty (Morphism (flatten R) (flatten S)) :=
    ⟨Lax369799Proofs.Pullbacks.trimMap f⟩
  change U.val = flatten R at hU
  rw [DirectResolution, hU]
  exact hf

end Lax369799Proofs.Flattening
