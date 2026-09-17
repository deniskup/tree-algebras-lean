import Lax369799Proofs.Flattening

namespace Lax369799Proofs.ContextCongruence
open Lax369799.RankedSystems Lax369799.Morphisms Lax369799.Flattening
open Lax369799Proofs.Pullbacks Lax369799Proofs.MorphismTheorems

noncomputable def flattenMapRaw {A B : RankedSet} {n : ℕ}
    (P : SetSystem B n) (F G : RankedMap B (SetSystem A))
    (f : ∀ r a, Morphism (F r a) (G r a)) :
    Map (Lax369799Proofs.Flattening.graph (relabel F P))
      (Lax369799Proofs.Flattening.graph (relabel G P)) := by
  let S := relabel F P
  let T := relabel G P
  let m (v : P.Vertex) := f (P.graph.label v).1 (P.graph.label v).2
  let raw : Map (Lax369799Proofs.Flattening.graph S) (Lax369799Proofs.Flattening.graph T) := {
    toFun := fun v => ⟨v.1, (m v.1).toFun v.2⟩
    initial := fun v hv => ⟨hv.1, (m v.1).initial v.2 hv.2⟩
    root := fun v hv => hv.elim
      (fun h => Or.inl ((m v.1).root v.2 h))
      (fun h => Or.inr ⟨h.1, (m v.1).initial v.2 h.2⟩)
    label := fun v => (m v.1).label v.2
    edge := by
      intro v d t ht
      rcases ht with ⟨w, hw, rfl⟩ | ⟨i, hi, ht⟩
      · exact Or.inl ⟨(m v.1).toFun w, (m v.1).edge v.2 d (.inl w) hw, rfl⟩
      · refine Or.inr ⟨i, (m v.1).edge v.2 d (.inr i) hi, ?_⟩
        rcases ht with ⟨w, hw, hw', rfl⟩ | ⟨j, hj, rfl⟩
        · exact Or.inl ⟨⟨w.1, (m w.1).toFun w.2⟩, hw, (m w.1).initial w.2 hw', rfl⟩
        · exact Or.inr ⟨j, hj, rfl⟩ }
  exact raw

noncomputable def flatten_label_morphism {A B : RankedSet} {n : ℕ}
    (P : SetSystem B n) (F G : RankedMap B (SetSystem A))
    (f : ∀ r a, Morphism (F r a) (G r a)) :
    Morphism (flatten (relabel F P)) (flatten (relabel G P)) :=
  trimMap (flattenMapRaw P F G f)

private theorem flatten_label_cover {A B : RankedSet} {n : ℕ}
    (P : SetSystem B n) (F G : RankedMap B (SetSystem A))
    (f : ∀ r a, Morphism (F r a) (G r a))
    (hf : ∀ r a, (f r a).LocallySurjective) :
    UnfoldsTo (flatten (relabel G P)) (flatten (relabel F P)) := by
  classical
  let S := relabel F P
  let T := relabel G P
  let m (v : P.Vertex) := f (P.graph.label v).1 (P.graph.label v).2
  have hm (v : P.Vertex) := hf (P.graph.label v).1 (P.graph.label v).2
  let raw := flattenMapRaw P F G f
  refine ⟨trimMap raw, trimMap_surjective raw ?_ ?_ ?_⟩
  · intro w hw
    obtain ⟨v, hv, he⟩ := (hm w.1).1 w.2 hw.2
    exact ⟨⟨w.1, v⟩, ⟨hw.1, hv⟩, by change Sigma.mk w.1 _ = w; rw [he]⟩
  · intro w hw
    rcases hw with hw | ⟨ho, hw⟩
    · obtain ⟨v, hv, he⟩ := (hm w.1).2.1 w.2 hw
      exact ⟨⟨w.1, v⟩, Or.inl hv, by change Sigma.mk w.1 _ = w; rw [he]⟩
    · obtain ⟨v, hv, he⟩ := (hm w.1).1 w.2 hw
      exact ⟨⟨w.1, v⟩, Or.inr ⟨ho, hv⟩, by change Sigma.mk w.1 _ = w; rw [he]⟩
  · intro v d t ht
    rcases ht with ⟨w, hw, rfl⟩ | ⟨i, hi, ht⟩
    · obtain ⟨s, hs, he⟩ := (hm v.1).2.2 v.2 d (.inl w) hw
      cases s with
      | inl u =>
        refine ⟨.inl ⟨v.1, u⟩, Or.inl ⟨u, hs, rfl⟩, ?_⟩
        have he := Sum.inl.inj he
        change (Sum.inl ⟨v.1, (m v.1).toFun u⟩ : ((v : T.Vertex) × (Inner T v).Vertex) ⊕ Fin n) = _
        rw [he]
        rfl
      | inr j => cases he
    · obtain ⟨s, hs, he⟩ := (hm v.1).2.2 v.2 d (.inr i) hi
      cases s with
      | inl u => cases he
      | inr j =>
        have he : j = i := Sum.inr.inj he
        subst j
        rcases ht with ⟨w, hw, hw', rfl⟩ | ⟨j, hj, rfl⟩
        · obtain ⟨u, hu, hue⟩ := (hm w.1).1 w.2 hw'
          refine ⟨.inl ⟨w.1, u⟩, Or.inr ⟨i, hs, Or.inl ⟨⟨w.1, u⟩, hw, hu, rfl⟩⟩, ?_⟩
          change Sum.inl ⟨w.1, (m w.1).toFun u⟩ = .inl w
          rw [hue]
        · exact ⟨.inr j, Or.inr ⟨i, hs, Or.inr ⟨j, hj, rfl⟩⟩, rfl⟩

private theorem plug_cover {A : RankedSet} {k n : ℕ} (C : SetContext A k n)
    {S T : SetSystem A k} (h : UnfoldsTo S T) : UnfoldsTo (plug C S) (plug C T) := by
  classical
  have hh : ∀ r a, UnfoldsTo (substitution S r a) (substitution T r a) := by
    intro r a
    cases a with
    | inl a => exact ⟨identity (atomic a), identity_surjective (atomic a)⟩
    | inr hkr =>
      obtain ⟨hkr⟩ := hkr
      subst r
      exact h
  exact flatten_label_cover C.system (substitution T) (substitution S)
    (fun r a => Classical.choose (hh r a)) (fun r a => Classical.choose_spec (hh r a))

/--
---
conclusion: Lax369799.FlatteningTheorems.unfold_context_congruence
---
Substitution preserves covering maps, including initial and root marks
and edges that return to the same component. Substitute a common cover
at the hole to obtain a common cover of the two plugged contexts.
-/
theorem unfold_context_congruence {A : RankedSet} {k n : ℕ}
    (C : SetContext A k n) (S T : SetSystem A k) (h : UnfoldEquivalent S T) :
    UnfoldEquivalent (plug C S) (plug C T) := by
  obtain ⟨U, hS, hT⟩ := h
  exact ⟨plug C U, plug_cover C hS, plug_cover C hT⟩

end Lax369799Proofs.ContextCongruence
