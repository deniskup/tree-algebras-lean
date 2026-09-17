import Lax369799Proofs.DeterministicNormalForms

set_option backward.isDefEq.respectTransparency false

namespace Lax369799Proofs.RawSystemFlattening
open Lax369799.RankedSystems Lax369799.Flattening Lax369799.Morphisms Lax369799.Algebras
open Lax369799Proofs.DeterministicNormalForms Lax369799Proofs.Pullbacks

theorem deterministic {A : RankedSet} {n : ℕ} {V : Type} [Fintype V]
    (G : Presentation (System A) n V) (r : V) (initialMark : G.initial = {r})
    (roots : G.root = ∅) (total : ∀ v d, d < (G.label v).1 → ∃! t, G.edge v d t) :
    (trim (rawFlatten G)).Deterministic := by
  classical
  let H := rawFlatten G
  let initial (v : V) := Classical.choose (G.label v).2.property.1
  have initial_spec (v : V) :
      (G.label v).2.val.graph.initial = {initial v} :=
    Classical.choose_spec (G.label v).2.property.1
  let outer (v : V) (i : Fin (G.label v).1) :=
    Classical.choose (total v i.val i.isLt)
  have outer_edge (v : V) (i : Fin (G.label v).1) :
      G.edge v i.val (outer v i) :=
    (Classical.choose_spec (total v i.val i.isLt)).1
  have outer_unique (v : V) (i : Fin (G.label v).1)
      (t : V ⊕ Fin n) (ht : G.edge v i.val t) : t = outer v i :=
    (Classical.choose_spec (total v i.val i.isLt)).2 t ht
  let next (v : V) (t : (G.label v).2.val.Vertex ⊕ Fin (G.label v).1) :
      ((v : V) × (G.label v).2.val.Vertex) ⊕ Fin n :=
    match t with
    | .inl w => .inl ⟨v, w⟩
    | .inr i => match outer v i with
      | .inl w => .inl ⟨w, initial w⟩
      | .inr j => .inr j
  have edge_iff (v : (v : V) × (G.label v).2.val.Vertex) (d : ℕ) (t) :
      H.edge v d t ↔ ∃ s, (G.label v.1).2.val.graph.edge v.2 d s ∧ t = next v.1 s := by
    constructor
    · rintro (⟨w, hw, rfl⟩ | ⟨i, hi, h⟩)
      · exact ⟨.inl w, hw, rfl⟩
      · refine ⟨.inr i, hi, ?_⟩
        rcases h with ⟨w, hw, hw', rfl⟩ | ⟨j, hj, rfl⟩
        · have he := outer_unique v.1 i (.inl w.1) hw
          have hin : w.2 = initial w.1 := by
            have h : (G.label w.1).2.val.graph.initial w.2 := hw'
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
          · change (G.label w).2.val.graph.initial (initial w)
            rw [initial_spec]; rfl
          · simp only [next, ho]
        | inr j =>
          refine Or.inr ⟨j, ?_, ?_⟩
          · have h := outer_edge v.1 i
            rw [ho] at h; exact h
          · simp only [next, ho]
  let i := r
  have hi : G.initial = {i} := initialMark
  have hdet : (trim H).Deterministic := by
    apply Lax369799Proofs.Yields.trim_deterministic H ⟨i, initial i⟩
    · ext v
      change (v.1 ∈ G.initial ∧ v.2 ∈ (G.label v.1).2.val.graph.initial) ↔ _
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
      change ((v.2 ∈ (G.label v.1).2.val.graph.root) ∨
        (v.1 ∈ G.root ∧ v.2 ∈ (G.label v.1).2.val.graph.initial)) ↔ False
      have hr : (G.label v.1).2.val.graph.root = ∅ := (G.label v.1).2.property.2.1
      rw [hr, roots]
      exact ⟨fun h => h.elim (fun h => h) (fun h => h.1), False.elim⟩
    · intro v d hd
      obtain ⟨s, hs, hu⟩ := (G.label v.1).2.property.2.2 v.2 d hd
      refine ⟨next v.1 s, (edge_iff v d _).mpr ⟨s, hs, rfl⟩, ?_⟩
      intro t ht
      obtain ⟨u, hu', he⟩ := (edge_iff v d t).mp ht
      rw [hu u hu'] at he
      exact he
  exact hdet

theorem evaluation {A : RankedSet} (E : Algebra A) (hE : UnfoldInvariant E)
    {n : ℕ} {V : Type} [Fintype V] (G : Presentation (System A) n V)
    (r : V) (initialMark : G.initial = {r}) (roots : G.root = ∅)
    (total : ∀ v d, d < (G.label v).1 → ∃! t, G.edge v d t) :
    E.eval n (relabelSystem E.eval ⟨trim G, Yields.trim_deterministic G r initialMark roots total⟩) =
      E.eval n ⟨trim (rawFlatten G), deterministic G r initialMark roots total⟩ := by
  let T : System (System A) n := ⟨trim G, Yields.trim_deterministic G r initialMark roots total⟩
  let R : System A n := ⟨trim (rawFlatten G), deterministic G r initialMark roots total⟩
  obtain ⟨U, hU⟩ := Flattening.flatten_system T
  have f : Morphism U.val R.val := by
    rw [hU]
    exact trimMap (flattenEmbedding G)
  have he := hE n U R ⟨U.val,
    ⟨MorphismTheorems.identity _, MorphismTheorems.identity_surjective _⟩,
    ⟨f, MorphismTheorems.system_morphism_locally_surjective U R f⟩⟩
  exact (E.associative n T U hU).trans he

end Lax369799Proofs.RawSystemFlattening
