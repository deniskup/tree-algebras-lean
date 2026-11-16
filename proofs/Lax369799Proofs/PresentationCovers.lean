import Lax369799.PresentationCovers

namespace Lax369799Proofs
open Lax369799.RankedSystems Lax369799.Morphisms Lax369799.PresentationCovers

/--
---
conclusion: Lax369799.PresentationCovers.trim_cover
---
Restrict the covering map to reachable vertices. Successors of reachable
vertices are reachable; initial and root vertices are reachable by empty paths.
-/
theorem trim_cover {A : RankedSet} {n : ℕ} {V : Type} [Fintype V]
    (S : Presentation A n V) (T : SetSystem A n) (f : Cover S T.graph) :
    UnfoldsTo T (trim S) := by
  classical
  let W := {v : V // S.Reachable v}
  let e : W ≃ Fin (Fintype.card W) := Fintype.equivFin W
  let g : (trim S).Vertex → V := fun v => (e.symm v).val
  have reaches (v : (trim S).Vertex) : S.Reachable (g v) := (e.symm v).property
  have reaches_next {v w : V} (hv : S.Reachable v) (d : ℕ)
      (he : S.edge v d (.inl w)) : S.Reachable w := by
    obtain ⟨r, hr, hp⟩ := hv
    exact ⟨r, hr, hp.tail ⟨d, he⟩⟩
  let m : Morphism (trim S) T := {
    toFun := fun v => f.toFun (g v)
    label := fun v => f.label (g v)
    initial := fun v hv => f.initial (g v) hv
    root := fun v hv => f.root (g v) hv
    edge := by
      intro v d t ht
      have h := f.edge (g v) d (Sum.map g id t) ht
      cases t <;> exact h }
  refine ⟨m, ?_, ?_, ?_⟩
  · intro w hw
    obtain ⟨v, hv, he⟩ := f.initial_lift w hw
    have hr : S.Reachable v := ⟨v, Or.inl hv, .refl⟩
    refine ⟨e ⟨v, hr⟩, ?_, ?_⟩
    · change S.initial (g (e ⟨v, hr⟩))
      simp only [g, Equiv.symm_apply_apply]
      exact hv
    · change f.toFun (g (e ⟨v, hr⟩)) = w
      simpa only [g, Equiv.symm_apply_apply] using he
  · intro w hw
    obtain ⟨v, hv, he⟩ := f.root_lift w hw
    have hr : S.Reachable v := ⟨v, Or.inr hv, .refl⟩
    refine ⟨e ⟨v, hr⟩, ?_, ?_⟩
    · change S.root (g (e ⟨v, hr⟩))
      simp only [g, Equiv.symm_apply_apply]
      exact hv
    · change f.toFun (g (e ⟨v, hr⟩)) = w
      simpa only [g, Equiv.symm_apply_apply] using he
  · intro v d t ht
    obtain ⟨s, hs, he⟩ := f.edge_lift (g v) d t ht
    cases s with
    | inl w =>
      have hw : S.Reachable w := reaches_next (reaches v) d hs
      refine ⟨Sum.inl (e ⟨w, hw⟩), ?_, ?_⟩
      · change S.edge (g v) d (.inl (g (e ⟨w, hw⟩)))
        simpa only [g, Equiv.symm_apply_apply] using hs
      · change Sum.inl (f.toFun (g (e ⟨w, hw⟩))) = t
        simpa only [g, Equiv.symm_apply_apply, Sum.map_inl] using he
    | inr i => exact ⟨Sum.inr i, hs, he⟩

namespace PresentationCovers

/--
---
conclusion: Lax369799.PresentationCovers.surjective_of_reachable
---
Lift a path from an initial vertex or a root to each target vertex.
-/
theorem surjective_of_reachable {A : RankedSet} {n : ℕ} {V W : Type}
    {S : Presentation A n V} {T : Presentation A n W} (f : Cover S T)
    (hT : ∀ w, T.Reachable w) : Function.Surjective f.toFun := by
  intro w
  obtain ⟨r, hr, hp⟩ := hT w
  have hbase : ∃ v, f.toFun v = r := by
    rcases hr with hr | hr
    · obtain ⟨v, _, hv⟩ := f.initial_lift r hr
      exact ⟨v, hv⟩
    · obtain ⟨v, _, hv⟩ := f.root_lift r hr
      exact ⟨v, hv⟩
  induction hp with
  | refl => exact hbase
  | @tail y z _ hyz ih =>
    obtain ⟨v, rfl⟩ := ih
    obtain ⟨d, hd⟩ := hyz
    obtain ⟨s, _, hs⟩ := f.edge_lift v d (.inl z) hd
    cases s with
    | inl u => exact ⟨u, Sum.inl.inj hs⟩
    | inr j => cases hs

end PresentationCovers
end Lax369799Proofs
