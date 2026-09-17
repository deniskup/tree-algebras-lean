import Lax369799Proofs.MorphismTheorems
import Mathlib.Data.Fintype.Prod

namespace Lax369799Proofs.Pullbacks
open Lax369799.RankedSystems Lax369799.Morphisms

private theorem morphism_ext {A : RankedSet} {n : ℕ} {S T : SetSystem A n}
    (f g : Morphism S T) (h : f.toFun = g.toFun) : f = g := by
  cases f
  cases g
  congr

structure Map {A : RankedSet} {n : ℕ} {V W : Type}
    (S : Presentation A n V) (T : Presentation A n W) where
  toFun : V → W
  initial : ∀ v, S.initial v → T.initial (toFun v)
  root : ∀ v, S.root v → T.root (toFun v)
  label : ∀ v, T.label (toFun v) = S.label v
  edge : ∀ v d t, S.edge v d t → T.edge (toFun v) d (Sum.map toFun id t)

noncomputable def index {A : RankedSet} {n : ℕ} {V : Type} [Fintype V]
    (S : Presentation A n V) : {v // S.Reachable v} ≃ (trim S).Vertex := by
  classical
  exact Fintype.equivFin _

noncomputable def vertex {A : RankedSet} {n : ℕ} {V : Type} [Fintype V]
    (S : Presentation A n V) (v : (trim S).Vertex) : V := (index S).symm v |>.val

theorem vertex_index {A : RankedSet} {n : ℕ} {V : Type} [Fintype V]
    (S : Presentation A n V) (v : V) (h : S.Reachable v) :
    vertex S (index S ⟨v, h⟩) = v := by simp [vertex]

theorem reachable_map {A : RankedSet} {n : ℕ} {V W : Type}
    {S : Presentation A n V} {T : Presentation A n W} (f : Map S T)
    {v : V} (hv : S.Reachable v) : T.Reachable (f.toFun v) := by
  obtain ⟨r, hr, hp⟩ := hv
  refine ⟨f.toFun r, hr.elim (fun h => Or.inl (f.initial r h))
    (fun h => Or.inr (f.root r h)), ?_⟩
  induction hp with
  | refl => exact .refl
  | @tail b c hp he ih =>
    obtain ⟨d, hd⟩ := he
    exact ih.tail ⟨d, f.edge b d (.inl c) hd⟩

noncomputable def project {A : RankedSet} {n : ℕ} {V : Type} [Fintype V]
    {S : Presentation A n V} {T : SetSystem A n} (f : Map S T.graph) :
    Morphism (trim S) T where
  toFun := fun v => f.toFun (vertex S v)
  initial := fun v h => f.initial _ h
  root := fun v h => f.root _ h
  label := fun v => f.label _
  edge := by
    intro v d t h
    have hh := f.edge (vertex S v) d (Sum.map (vertex S) id t) h
    cases t <;> exact hh

noncomputable def lift {A : RankedSet} {n : ℕ} {V : Type} [Fintype V]
    {S : SetSystem A n} {T : Presentation A n V} (f : Map S.graph T) :
    Morphism S (trim T) where
  toFun := fun v => index T ⟨f.toFun v, reachable_map f (S.reachable v)⟩
  initial := by
    intro v h
    change T.initial (vertex T (index T _))
    rw [vertex_index]
    exact f.initial v h
  root := by
    intro v h
    change T.root (vertex T (index T _))
    rw [vertex_index]
    exact f.root v h
  label := by
    intro v
    change T.label (vertex T (index T _)) = _
    rw [vertex_index]
    exact f.label v
  edge := by
    intro v d t h
    have hh := f.edge v d t h
    cases t with
    | inl w =>
      change T.edge (vertex T (index T _)) d (.inl (vertex T (index T _)))
      simpa only [vertex_index, Sum.map_inl, Sum.map_inr, id_eq] using hh
    | inr i =>
      change T.edge (vertex T (index T _)) d (.inr i)
      simpa only [vertex_index, Sum.map_inl, Sum.map_inr, id_eq] using hh

noncomputable def trimMap {A : RankedSet} {n : ℕ} {V W : Type} [Fintype V] [Fintype W]
    {S : Presentation A n V} {T : Presentation A n W} (f : Map S T) :
    Morphism (trim S) (trim T) :=
  lift {
    toFun := fun v => f.toFun (vertex S v)
    initial := fun v h => f.initial _ h
    root := fun v h => f.root _ h
    label := fun v => f.label _
    edge := by
      intro v d t h
      have hh := f.edge (vertex S v) d (Sum.map (vertex S) id t) h
      cases t <;> exact hh }

theorem vertex_injective {A : RankedSet} {n : ℕ} {V : Type} [Fintype V]
    (S : Presentation A n V) : Function.Injective (vertex S) := by
  intro v w h
  apply (index S).symm.injective
  exact Subtype.ext h

theorem vertex_trimMap {A : RankedSet} {n : ℕ} {V W : Type} [Fintype V] [Fintype W]
    {S : Presentation A n V} {T : Presentation A n W} (f : Map S T) (v) :
    vertex T ((trimMap f).toFun v) = f.toFun (vertex S v) := by
  exact vertex_index T _ _

theorem trimMap_surjective {A : RankedSet} {n : ℕ} {V W : Type} [Fintype V] [Fintype W]
    {S : Presentation A n V} {T : Presentation A n W} (f : Map S T)
    (hi : ∀ w, T.initial w → ∃ v, S.initial v ∧ f.toFun v = w)
    (hr : ∀ w, T.root w → ∃ v, S.root v ∧ f.toFun v = w)
    (he : ∀ v d t, T.edge (f.toFun v) d t →
      ∃ s, S.edge v d s ∧ Sum.map f.toFun id s = t) :
    (trimMap f).LocallySurjective := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · intro w hw
    obtain ⟨v, hv, hvw⟩ := hi (vertex T w) hw
    have hv' : S.Reachable v := ⟨v, Or.inl hv, .refl⟩
    refine ⟨index S ⟨v, hv'⟩, ?_, ?_⟩
    · change S.initial (vertex S (index S _))
      rw [vertex_index]; exact hv
    · apply vertex_injective T
      rw [vertex_trimMap, vertex_index]
      exact hvw
  · intro w hw
    obtain ⟨v, hv, hvw⟩ := hr (vertex T w) hw
    have hv' : S.Reachable v := ⟨v, Or.inr hv, .refl⟩
    refine ⟨index S ⟨v, hv'⟩, ?_, ?_⟩
    · change S.root (vertex S (index S _))
      rw [vertex_index]; exact hv
    · apply vertex_injective T
      rw [vertex_trimMap, vertex_index]
      exact hvw
  · intro v d t ht
    change T.edge (vertex T ((trimMap f).toFun v)) d (Sum.map (vertex T) id t) at ht
    rw [vertex_trimMap] at ht
    obtain ⟨s, hs, hst⟩ := he (vertex S v) d _ ht
    have maps_inj : Function.Injective (Sum.map (vertex T) (id : Fin n → Fin n)) := by
      intro a b h
      cases a <;> cases b
      · exact congrArg Sum.inl (vertex_injective T (Sum.inl.inj h))
      · cases h
      · cases h
      · exact congrArg Sum.inr (Sum.inr.inj h)
    cases s with
    | inl w =>
      have hw : S.Reachable w := by
        obtain ⟨r, hr, hp⟩ := ((index S).symm v).property
        exact ⟨r, hr, hp.tail ⟨d, hs⟩⟩
      refine ⟨.inl (index S ⟨w, hw⟩), ?_, ?_⟩
      · change S.edge (vertex S v) d (.inl (vertex S (index S _)))
        rw [vertex_index]; exact hs
      · apply maps_inj
        simpa only [Sum.map_inl, vertex_trimMap, vertex_index] using hst
    | inr i =>
      refine ⟨.inr i, hs, ?_⟩
      apply maps_inj
      exact hst

private def Fiber {A : RankedSet} {n : ℕ} {S T U : SetSystem A n}
    (f : Morphism S U) (g : Morphism T U) :=
  {p : S.Vertex × T.Vertex // f.toFun p.1 = g.toFun p.2}

private noncomputable instance {A : RankedSet} {n : ℕ} {S T U : SetSystem A n}
    (f : Morphism S U) (g : Morphism T U) : Fintype (Fiber f g) := by
  classical
  unfold Fiber
  infer_instance

private def graph {A : RankedSet} {n : ℕ} {S T U : SetSystem A n}
    (f : Morphism S U) (g : Morphism T U) : Presentation A n (Fiber f g) where
  label := fun v => S.graph.label v.val.1
  initial := fun v => S.graph.initial v.val.1 ∧ T.graph.initial v.val.2
  root := fun v => S.graph.root v.val.1 ∧ T.graph.root v.val.2
  edge := fun v d t =>
    S.graph.edge v.val.1 d (Sum.map (fun w => w.val.1) id t) ∧
    T.graph.edge v.val.2 d (Sum.map (fun w => w.val.2) id t)
  direction_valid := fun _ _ _ h => S.graph.direction_valid _ _ _ h.1

private def first {A : RankedSet} {n : ℕ} {S T U : SetSystem A n}
    (f : Morphism S U) (g : Morphism T U) : Map (graph f g) S.graph where
  toFun := fun v => v.val.1
  initial := fun _ h => h.1
  root := fun _ h => h.1
  label := fun _ => rfl
  edge := fun _ _ _ h => h.1

private def second {A : RankedSet} {n : ℕ} {S T U : SetSystem A n}
    (f : Morphism S U) (g : Morphism T U) : Map (graph f g) T.graph where
  toFun := fun v => v.val.2
  initial := fun _ h => h.2
  root := fun _ h => h.2
  label := by
    intro v
    exact (g.label v.val.2).symm.trans ((congrArg U.graph.label v.property.symm).trans (f.label v.val.1))
  edge := fun _ _ _ h => h.2

private def pair {A : RankedSet} {n : ℕ} {S T U : SetSystem A n}
    (f : Morphism S U) (g : Morphism T U) (V : SetSystem A n)
    (a : Morphism V S) (b : Morphism V T)
    (h : f.toFun ∘ a.toFun = g.toFun ∘ b.toFun) : Map V.graph (graph f g) where
  toFun := fun v => ⟨(a.toFun v, b.toFun v), congrFun h v⟩
  initial := fun v hv => ⟨a.initial v hv, b.initial v hv⟩
  root := fun v hv => ⟨a.root v hv, b.root v hv⟩
  label := fun v => a.label v
  edge := by
    intro v d t ht
    have ha := a.edge v d t ht
    have hb := b.edge v d t ht
    cases t <;> exact ⟨ha, hb⟩

theorem project_surjective {A : RankedSet} {n : ℕ} {V : Type} [Fintype V]
    {S : Presentation A n V} {T : SetSystem A n} (f : Map S T.graph)
    (hi : ∀ w, T.graph.initial w → ∃ v, S.initial v ∧ f.toFun v = w)
    (hr : ∀ w, T.graph.root w → ∃ v, S.root v ∧ f.toFun v = w)
    (he : ∀ v d t, T.graph.edge (f.toFun v) d t →
      ∃ s, S.edge v d s ∧ Sum.map f.toFun id s = t) :
    (project f).LocallySurjective := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · intro w hw
    obtain ⟨v, hv, hvw⟩ := hi w hw
    have hv' : S.Reachable v := ⟨v, Or.inl hv, .refl⟩
    refine ⟨index S ⟨v, hv'⟩, ?_, ?_⟩
    · change S.initial (vertex S (index S _))
      rw [vertex_index]; exact hv
    · change f.toFun (vertex S (index S _)) = w
      rw [vertex_index]; exact hvw
  · intro w hw
    obtain ⟨v, hv, hvw⟩ := hr w hw
    have hv' : S.Reachable v := ⟨v, Or.inr hv, .refl⟩
    refine ⟨index S ⟨v, hv'⟩, ?_, ?_⟩
    · change S.root (vertex S (index S _))
      rw [vertex_index]; exact hv
    · change f.toFun (vertex S (index S _)) = w
      rw [vertex_index]; exact hvw
  · intro v d t ht
    obtain ⟨s, hs, hst⟩ := he (vertex S v) d t ht
    cases s with
    | inl w =>
      have hw : S.Reachable w := by
        obtain ⟨r, hr, hp⟩ := ((index S).symm v).property
        exact ⟨r, hr, hp.tail ⟨d, hs⟩⟩
      refine ⟨.inl (index S ⟨w, hw⟩), ?_, ?_⟩
      · change S.edge (vertex S v) d (.inl (vertex S (index S _)))
        rw [vertex_index]; exact hs
      · change Sum.inl (f.toFun (vertex S (index S _))) = t
        rw [vertex_index]; exact hst
    | inr i => exact ⟨.inr i, hs, hst⟩

private theorem second_surjective {A : RankedSet} {n : ℕ} {S T U : SetSystem A n}
    (f : Morphism S U) (g : Morphism T U) (hf : f.LocallySurjective) :
    (project (second f g)).LocallySurjective := by
  apply project_surjective
  · intro w hw
    obtain ⟨v, hv, he⟩ := hf.1 _ (g.initial w hw)
    exact ⟨⟨(v, w), he⟩, ⟨hv, hw⟩, rfl⟩
  · intro w hw
    obtain ⟨v, hv, he⟩ := hf.2.1 _ (g.root w hw)
    exact ⟨⟨(v, w), he⟩, ⟨hv, hw⟩, rfl⟩
  · intro v d t ht
    have hg := g.edge v.val.2 d t ht
    rw [← v.property] at hg
    obtain ⟨s, hs, he⟩ := hf.2.2 v.val.1 d _ hg
    cases t with
    | inl w =>
      cases s with
      | inl u => exact ⟨.inl ⟨(u, w), Sum.inl.inj he⟩, ⟨hs, ht⟩, rfl⟩
      | inr i => cases he
    | inr i =>
      cases s with
      | inl u => cases he
      | inr j =>
        have hj : j = i := Sum.inr.inj he
        subst j
        exact ⟨.inr i, ⟨hs, ht⟩, rfl⟩

private theorem first_surjective {A : RankedSet} {n : ℕ} {S T U : SetSystem A n}
    (f : Morphism S U) (g : Morphism T U) (hg : g.LocallySurjective) :
    (project (first f g)).LocallySurjective := by
  apply project_surjective
  · intro v hv
    obtain ⟨w, hw, he⟩ := hg.1 _ (f.initial v hv)
    exact ⟨⟨(v, w), he.symm⟩, ⟨hv, hw⟩, rfl⟩
  · intro v hv
    obtain ⟨w, hw, he⟩ := hg.2.1 _ (f.root v hv)
    exact ⟨⟨(v, w), he.symm⟩, ⟨hv, hw⟩, rfl⟩
  · intro v d t ht
    have hf := f.edge v.val.1 d t ht
    rw [v.property] at hf
    obtain ⟨s, hs, he⟩ := hg.2.2 v.val.2 d _ hf
    cases t with
    | inl w =>
      cases s with
      | inl u => exact ⟨.inl ⟨(w, u), (Sum.inl.inj he).symm⟩, ⟨ht, hs⟩, rfl⟩
      | inr i => cases he
    | inr i =>
      cases s with
      | inl u => cases he
      | inr j =>
        have hj : j = i := Sum.inr.inj he
        subst j
        exact ⟨.inr i, ⟨ht, hs⟩, rfl⟩

/--
---
conclusion: Lax369799.MorphismTheorems.pullback
---
Take the reachable part of the fiber product of vertex sets. Edges and
marks are intersections of their inverse images under the projections.
-/
theorem pullback {A : RankedSet} {n : ℕ} {S T U : SetSystem A n}
    (f : Morphism S U) (g : Morphism T U) :
    ∃ (P : SetSystem A n) (p : Morphism P S) (q : Morphism P T),
      f.toFun ∘ p.toFun = g.toFun ∘ q.toFun ∧
      (∀ (V : SetSystem A n) (a : Morphism V S) (b : Morphism V T),
        f.toFun ∘ a.toFun = g.toFun ∘ b.toFun →
        ∃! h : Morphism V P, p.toFun ∘ h.toFun = a.toFun ∧ q.toFun ∘ h.toFun = b.toFun) ∧
      (f.LocallySurjective → q.LocallySurjective) ∧
      (g.LocallySurjective → p.LocallySurjective) := by
  classical
  refine ⟨trim (graph f g), project (first f g), project (second f g), ?_, ?_,
    second_surjective f g, first_surjective f g⟩
  · funext v
    exact (vertex (graph f g) v).property
  · intro V a b hab
    refine ⟨lift (pair f g V a b hab), ⟨?_, ?_⟩, ?_⟩
    · funext v
      change (vertex (graph f g) (index (graph f g) _)).val.1 = a.toFun v
      rw [vertex_index]; rfl
    · funext v
      change (vertex (graph f g) (index (graph f g) _)).val.2 = b.toFun v
      rw [vertex_index]; rfl
    · intro h ⟨hp, hq⟩
      have hfun : h.toFun = (lift (pair f g V a b hab)).toFun := by
        funext v
        apply (index (graph f g)).symm.injective
        apply Subtype.ext
        apply Subtype.ext
        apply Prod.ext
        · have hh := congrFun hp v
          change (vertex (graph f g) (h.toFun v)).val.1 = a.toFun v at hh
          simpa only [lift, vertex, Equiv.symm_apply_apply, pair] using hh
        · have hh := congrFun hq v
          change (vertex (graph f g) (h.toFun v)).val.2 = b.toFun v at hh
          simpa only [lift, vertex, Equiv.symm_apply_apply, pair] using hh
      exact morphism_ext _ _ hfun

end Lax369799Proofs.Pullbacks
