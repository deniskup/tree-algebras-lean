import Lax369799Proofs.Pullbacks
import Lax369799Proofs.UnfoldEquivalence

namespace Lax369799Proofs.Yields
open Lax369799.RankedSystems Lax369799.Morphisms
open Lax369799Proofs.Pullbacks Lax369799Proofs.MorphismTheorems

theorem trim_deterministic {A : RankedSet} {n : ℕ} {V : Type} [Fintype V]
    (G : Presentation A n V) (r : V) (hi : G.initial = {r}) (hr : G.root = ∅)
    (he : ∀ v d, d < (G.label v).1 → ∃! t, G.edge v d t) :
    (trim G).Deterministic := by
  classical
  have rr : G.Reachable r := ⟨r, Or.inl (by rw [hi]; rfl), .refl⟩
  have inj : Function.Injective (vertex G) := by
    intro v w h
    apply (index G).symm.injective
    exact Subtype.ext h
  refine ⟨⟨index G ⟨r, rr⟩, ?_⟩, ?_, ?_⟩
  · ext v
    change G.initial (vertex G v) ↔ v = index G ⟨r, rr⟩
    rw [hi]
    constructor
    · intro h
      apply inj
      rw [vertex_index]
      exact h
    · rintro rfl
      rw [vertex_index]
      rfl
  · ext v
    change G.root (vertex G v) ↔ False
    rw [hr]
    rfl
  · intro v d hd
    obtain ⟨t, ht, hu⟩ := he (vertex G v) d hd
    have exists_target : ∃ s : (trim G).Vertex ⊕ Fin n, Sum.map (vertex G) id s = t := by
      cases t with
      | inl w =>
        have hw : G.Reachable w := by
          obtain ⟨r, hr, hp⟩ := ((index G).symm v).property
          exact ⟨r, hr, hp.tail ⟨d, ht⟩⟩
        exact ⟨.inl (index G ⟨w, hw⟩), by simp only [Sum.map_inl, vertex_index]⟩
      | inr i => exact ⟨.inr i, rfl⟩
    obtain ⟨s, hs⟩ := exists_target
    refine ⟨s, ?_, ?_⟩
    · change G.edge (vertex G v) d (Sum.map (vertex G) id s)
      rw [hs]; exact ht
    · intro u hu'
      have hu'' := hu _ hu'
      have eqmaps : Sum.map (vertex G) id u = Sum.map (vertex G) id s := hu''.trans hs.symm
      cases u <;> cases s <;> simp only [Sum.map_inl, Sum.map_inr, id_eq] at eqmaps ⊢
      · exact congrArg Sum.inl (inj (Sum.inl.inj eqmaps))
      · cases eqmaps
      · cases eqmaps
      · exact congrArg Sum.inr (Sum.inr.inj eqmaps)

private theorem resolution_exists {A : RankedSet} {n : ℕ} (S : SetSystem A n)
    (hi : ∃ r, r ∈ S.graph.initial)
    (ht : ∀ v d, d < (S.graph.label v).1 → ∃ t, S.graph.edge v d t) :
    ∃ D : System A n, Nonempty (Morphism D.val S) := by
  classical
  obtain ⟨r, hr⟩ := hi
  let chosen (v : S.Vertex) (d : ℕ) (h : d < (S.graph.label v).1) := Classical.choose (ht v d h)
  let G : Presentation A n S.Vertex := {
    label := S.graph.label
    initial := {r}
    root := ∅
    edge := fun v d t => ∃ h : d < (S.graph.label v).1, t = chosen v d h
    direction_valid := fun _ _ _ h => h.choose }
  have det : (trim G).Deterministic := trim_deterministic G r rfl rfl (by
    intro v d hd
    refine ⟨chosen v d hd, ⟨hd, rfl⟩, ?_⟩
    rintro t ⟨h, rfl⟩
    rfl)
  let m : Map G S.graph := {
    toFun := id
    initial := by intro v hv; change v = r at hv; subst v; exact hr
    root := by intro v hv; exact False.elim hv
    label := fun _ => rfl
    edge := by
      rintro v d t ⟨h, rfl⟩
      have hh := Classical.choose_spec (ht v d h)
      simpa only [Sum.map_id_id, id_eq, chosen] using hh }
  exact ⟨⟨trim G, det⟩, ⟨project m⟩⟩

private theorem lift_resolution {A : RankedSet} {n : ℕ} {S T : SetSystem A n}
    (f : Morphism S T) (hf : f.LocallySurjective) (D : System A n)
    (a : Morphism D.val T) :
    ∃ E : System A n, Nonempty (Morphism E.val S) ∧ UnfoldsTo D.val E.val := by
  obtain ⟨P, p, q, _, _, hq, _⟩ := pullback f a
  have hq := hq hf
  have hi : ∃ r, r ∈ P.graph.initial := by
    obtain ⟨i, hi⟩ := D.property.1
    obtain ⟨r, hr, _⟩ := hq.1 i (by rw [hi]; rfl)
    exact ⟨r, hr⟩
  have ht : ∀ v d, d < (P.graph.label v).1 → ∃ t, P.graph.edge v d t := by
    intro v d hd
    obtain ⟨t, ht, _⟩ := D.property.2.2 (q.toFun v) d (by rw [q.label]; exact hd)
    obtain ⟨s, hs, _⟩ := hq.2.2 v d t ht
    exact ⟨s, hs⟩
  obtain ⟨E, ⟨e⟩⟩ := resolution_exists P hi ht
  exact ⟨E, ⟨compose e p⟩, ⟨compose e q, system_morphism_locally_surjective E D (compose e q)⟩⟩

private def rooted {A : RankedSet} {n : ℕ} (S : SetSystem A n) : SetSystem A n where
  size := S.size
  graph := { S.graph with initial := S.graph.root, root := S.graph.root ∪ S.graph.initial }
  reachable := by
    intro v
    obtain ⟨r, hr, hp⟩ := S.reachable v
    exact ⟨r, Or.inr (hr.elim Or.inr Or.inl), hp⟩

private def rootedMap {A : RankedSet} {n : ℕ} {S T : SetSystem A n}
    (f : Morphism S T) : Morphism (rooted S) (rooted T) where
  toFun := f.toFun
  initial := f.root
  root := fun v h => h.elim (fun h => Or.inl (f.root v h)) (fun h => Or.inr (f.initial v h))
  label := f.label
  edge := f.edge

private theorem rooted_surjective {A : RankedSet} {n : ℕ} {S T : SetSystem A n}
    (f : Morphism S T) (hf : f.LocallySurjective) : (rootedMap f).LocallySurjective := by
  refine ⟨hf.2.1, ?_, hf.2.2⟩
  intro w hw
  rcases hw with hw | hw
  · obtain ⟨v, hv, he⟩ := hf.2.1 w hw
    exact ⟨v, Or.inl hv, he⟩
  · obtain ⟨v, hv, he⟩ := hf.1 w hw
    exact ⟨v, Or.inr hv, he⟩

private noncomputable def rootProjection {A : RankedSet} {n : ℕ} (S : SetSystem A n) :
    Morphism (uproot S) (rooted S) :=
  project {
    toFun := id
    initial := fun _ h => h
    root := fun _ h => False.elim h
    label := fun _ => rfl
    edge := by intro v d t h; cases t <;> exact h }

private noncomputable def rootResolution {A : RankedSet} {n : ℕ} {S : SetSystem A n}
    (D : System A n) (f : Morphism D.val (rooted S)) : Morphism D.val (uproot S) :=
  lift {
    toFun := f.toFun
    initial := f.initial
    root := by intro v hv; rw [D.property.2.1] at hv; exact False.elim hv
    label := f.label
    edge := f.edge }

private theorem initial_yield_forward {A : RankedSet} {n : ℕ} {S T : SetSystem A n}
    (f : Morphism S T) {U : System A n} (h : InitYield S U) : InitYield T U := by
  obtain ⟨D, ⟨d⟩, hd⟩ := h
  exact ⟨D, ⟨compose d f⟩, hd⟩

private theorem initial_yield_backward {A : RankedSet} {n : ℕ} {S T : SetSystem A n}
    (f : Morphism S T) (hf : f.LocallySurjective)
    {U : System A n} (h : InitYield T U) : InitYield S U := by
  obtain ⟨D, ⟨d⟩, ⟨u, hu⟩⟩ := h
  obtain ⟨E, he, ⟨e, he'⟩⟩ := lift_resolution f hf D d
  obtain ⟨c, _, hc⟩ := composition e u
  exact ⟨E, he, ⟨c, hc he' hu⟩⟩

private theorem yield_forward {A : RankedSet} {n : ℕ} {S T : SetSystem A n}
    (f : Morphism S T) : YieldBelow S T := by
  intro U h
  rcases h with ⟨V, hv, rfl⟩ | ⟨V, ⟨D, ⟨d⟩, hd⟩, rfl⟩
  · exact Or.inl ⟨V, initial_yield_forward f hv, rfl⟩
  · exact Or.inr ⟨V, ⟨D, ⟨rootResolution D
      (compose (compose d (rootProjection S)) (rootedMap f))⟩, hd⟩, rfl⟩

/--
---
conclusion: Lax369799.MorphismTheorems.morphism_yields
---
Compose resolutions for preservation. For a locally surjective map,
pull back a resolution and choose one successor in each direction.
Apply the same argument to roots to obtain preservation of root yields.
-/
theorem morphism_yields {A : RankedSet} {n : ℕ} {S T : SetSystem A n}
    (f : Morphism S T) : YieldBelow S T ∧ (f.LocallySurjective → YieldEquivalent S T) := by
  refine ⟨yield_forward f, ?_⟩
  intro hf U
  refine ⟨yield_forward f U, ?_⟩
  intro h
  rcases h with ⟨V, hv, rfl⟩ | ⟨V, ⟨D, ⟨d⟩, ⟨u, hu⟩⟩, rfl⟩
  · exact Or.inl ⟨V, initial_yield_backward f hf hv, rfl⟩
  · obtain ⟨E, ⟨e⟩, ⟨c, hc⟩⟩ := lift_resolution (rootedMap f) (rooted_surjective f hf)
      D (compose d (rootProjection T))
    obtain ⟨j, _, hj⟩ := composition c u
    exact Or.inr ⟨V, ⟨E, ⟨rootResolution E e⟩, ⟨j, hj hc hu⟩⟩, rfl⟩

/--
---
conclusion: Lax369799.MorphismTheorems.system_yield_equivalence
---
Common covers have identical yields. Conversely, a system is one of its
own initial yields, so yield equivalence supplies a common system cover.
-/
theorem system_yield_equivalence {A : RankedSet} {n : ℕ} (S T : System A n) :
    UnfoldEquivalent S.val T.val ↔ YieldEquivalent S.val T.val := by
  constructor
  · rintro ⟨U, ⟨s, hs⟩, ⟨t, ht⟩⟩ V
    exact ((morphism_yields s).2 hs V).symm.trans ((morphism_yields t).2 ht V)
  · intro h
    have self : Yield S.val S.val := Or.inl ⟨S,
      ⟨S, ⟨identity S.val⟩, ⟨identity S.val, identity_surjective S.val⟩⟩, rfl⟩
    rcases (h S.val).mp self with ⟨U, ⟨D, ⟨d⟩, hu⟩, he⟩ | ⟨U, _, he⟩
    · have hus : U = S := Subtype.ext he.symm
      subst U
      exact ⟨D.val, hu, ⟨d, system_morphism_locally_surjective D T d⟩⟩
    · obtain ⟨i, hi⟩ := S.property.1
      have hh : S.val.graph.initial = ∅ := by rw [he]; rfl
      rw [hh] at hi
      have : i ∈ (∅ : Set S.val.Vertex) := by rw [hi]; rfl
      exact False.elim this

end Lax369799Proofs.Yields
