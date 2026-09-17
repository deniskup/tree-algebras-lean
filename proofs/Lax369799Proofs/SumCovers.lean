import Lax369799Proofs.Pullbacks
import Lax369799.PresentationCovers

namespace Lax369799Proofs.SumCovers
open Lax369799.RankedSystems Lax369799.Morphisms Lax369799.PresentationCovers
open Lax369799Proofs.Pullbacks

noncomputable def combine {A : RankedSet} {n : ℕ} {V W : Type}
    (S : Presentation A n V) (T : Presentation A n W) : Presentation A n (V ⊕ W) where
  label := Sum.elim S.label T.label
  initial := Sum.elim S.initial T.initial
  root := Sum.elim S.root T.root
  edge := fun v d t => match v with
    | .inl v => ∃ t', S.edge v d t' ∧ t = Sum.map Sum.inl id t'
    | .inr v => ∃ t', T.edge v d t' ∧ t = Sum.map Sum.inr id t'
  direction_valid := by
    intro v d t h
    cases v with
    | inl v => obtain ⟨t', ht, _⟩ := h; exact S.direction_valid v d t' ht
    | inr v => obtain ⟨t', ht, _⟩ := h; exact T.direction_valid v d t' ht

theorem sum_eq_trim {A : RankedSet} {n : ℕ} (S T : SetSystem A n) :
    sum S T = trim (combine S.graph T.graph) := by
  unfold sum combine
  congr 1
  congr 1
  funext v d t
  cases v <;> rfl

def identity {A : RankedSet} {n : ℕ} {V : Type} (G : Presentation A n V) : Cover G G where
  toFun := id
  label := fun _ => rfl
  initial := fun _ h => h
  root := fun _ h => h
  edge := by intro v d t h; cases t <;> exact h
  initial_lift := fun w hw => ⟨w, hw, rfl⟩
  root_lift := fun w hw => ⟨w, hw, rfl⟩
  edge_lift := by intro v d t h; exact ⟨t, h, by cases t <;> rfl⟩

theorem trim_cover {A : RankedSet} {n : ℕ} {V W : Type} [Fintype V] [Fintype W]
    {S : Presentation A n V} {T : Presentation A n W} (f : Cover S T) :
    UnfoldsTo (trim T) (trim S) := by
  let m : Map S T := ⟨f.toFun, f.initial, f.root, f.label, f.edge⟩
  exact ⟨trimMap m, trimMap_surjective m f.initial_lift f.root_lift f.edge_lift⟩

noncomputable def combineCover {A : RankedSet} {n : ℕ} {V V' W W' : Type}
    {S : Presentation A n V} {S' : Presentation A n V'}
    {T : Presentation A n W} {T' : Presentation A n W'}
    (f : Cover S S') (g : Cover T T') : Cover (combine S T) (combine S' T') where
  toFun := Sum.map f.toFun g.toFun
  label := by intro v; cases v with | inl v => exact f.label v | inr v => exact g.label v
  initial := by intro v h; cases v with | inl v => exact f.initial v h | inr v => exact g.initial v h
  root := by intro v h; cases v with | inl v => exact f.root v h | inr v => exact g.root v h
  edge := by
    intro v d t ht
    cases v with
    | inl v =>
      obtain ⟨s, hs, rfl⟩ := ht
      exact ⟨Sum.map f.toFun id s, f.edge v d s hs, by cases s <;> rfl⟩
    | inr v =>
      obtain ⟨s, hs, rfl⟩ := ht
      exact ⟨Sum.map g.toFun id s, g.edge v d s hs, by cases s <;> rfl⟩
  initial_lift := by
    intro w hw
    cases w with
    | inl w => obtain ⟨v, hv, rfl⟩ := f.initial_lift w hw; exact ⟨.inl v, hv, rfl⟩
    | inr w => obtain ⟨v, hv, rfl⟩ := g.initial_lift w hw; exact ⟨.inr v, hv, rfl⟩
  root_lift := by
    intro w hw
    cases w with
    | inl w => obtain ⟨v, hv, rfl⟩ := f.root_lift w hw; exact ⟨.inl v, hv, rfl⟩
    | inr w => obtain ⟨v, hv, rfl⟩ := g.root_lift w hw; exact ⟨.inr v, hv, rfl⟩
  edge_lift := by
    intro v d t ht
    cases v with
    | inl v =>
      obtain ⟨s, hs, rfl⟩ := ht
      obtain ⟨u, hu, he⟩ := f.edge_lift v d s hs
      refine ⟨Sum.map Sum.inl id u, ⟨u, hu, rfl⟩, ?_⟩
      rw [← he]; cases u <;> rfl
    | inr v =>
      obtain ⟨s, hs, rfl⟩ := ht
      obtain ⟨u, hu, he⟩ := g.edge_lift v d s hs
      refine ⟨Sum.map Sum.inr id u, ⟨u, hu, rfl⟩, ?_⟩
      rw [← he]; cases u <;> rfl

noncomputable def enumerate {A : RankedSet} {n : ℕ} {V : Type} [Fintype V]
    (G : Presentation A n V) (h : ∀ v, G.Reachable v) : Cover G (trim G).graph where
  toFun := fun v => index G ⟨v, h v⟩
  label := by intro v; exact congrArg G.label (vertex_index G v (h v))
  initial := by intro v hv; change G.initial (vertex G (index G _)); rw [vertex_index]; exact hv
  root := by intro v hv; change G.root (vertex G (index G _)); rw [vertex_index]; exact hv
  edge := by
    intro v d t ht
    cases t with
    | inl w =>
      change G.edge (vertex G (index G _)) d (.inl (vertex G (index G _)))
      rw [vertex_index, vertex_index]; exact ht
    | inr i =>
      change G.edge (vertex G (index G _)) d (.inr i)
      rw [vertex_index]; exact ht
  initial_lift := by
    intro w hw
    refine ⟨vertex G w, hw, ?_⟩
    apply (index G).symm.injective
    simp only [Equiv.symm_apply_apply]
    rfl
  root_lift := by
    intro w hw
    refine ⟨vertex G w, hw, ?_⟩
    apply (index G).symm.injective
    simp only [Equiv.symm_apply_apply]
    rfl
  edge_lift := by
    intro v d t ht
    change G.edge (vertex G (index G _)) d (Sum.map (vertex G) id t) at ht
    rw [vertex_index] at ht
    refine ⟨Sum.map (vertex G) id t, ht, ?_⟩
    cases t with
    | inl w =>
      apply congrArg Sum.inl
      apply (index G).symm.injective
      simp only [Equiv.symm_apply_apply]
      rfl
    | inr i => rfl

theorem combine_reachable {A : RankedSet} {n : ℕ} {V W : Type}
    (S : Presentation A n V) (T : Presentation A n W)
    (hS : ∀ v, S.Reachable v) (hT : ∀ v, T.Reachable v) :
    ∀ v, (combine S T).Reachable v := by
  let l : Map S (combine S T) := {
    toFun := Sum.inl
    initial := fun _ h => h
    root := fun _ h => h
    label := fun _ => rfl
    edge := fun v d t h => ⟨t, h, rfl⟩ }
  let r : Map T (combine S T) := {
    toFun := Sum.inr
    initial := fun _ h => h
    root := fun _ h => h
    label := fun _ => rfl
    edge := fun v d t h => ⟨t, h, rfl⟩ }
  intro v
  cases v with
  | inl v => exact reachable_map l (hS v)
  | inr v => exact reachable_map r (hT v)

noncomputable def associate {A : RankedSet} {n : ℕ} {V W X : Type}
    (S : Presentation A n V) (T : Presentation A n W) (U : Presentation A n X) :
    Cover (combine (combine S T) U) (combine S (combine T U)) where
  toFun := (Equiv.sumAssoc V W X).toFun
  label := by rintro ((v | v) | v) <;> rfl
  initial := by rintro ((v | v) | v) h <;> exact h
  root := by rintro ((v | v) | v) h <;> exact h
  edge := by
    rintro ((v | v) | v) d t ht
    · obtain ⟨s, ⟨r, hr, rfl⟩, rfl⟩ := ht
      exact ⟨r, hr, by cases r <;> rfl⟩
    · obtain ⟨s, ⟨r, hr, rfl⟩, rfl⟩ := ht
      exact ⟨Sum.map Sum.inl id r, ⟨r, hr, rfl⟩, by cases r <;> rfl⟩
    · obtain ⟨r, hr, rfl⟩ := ht
      exact ⟨Sum.map Sum.inr id r, ⟨r, hr, rfl⟩, by cases r <;> rfl⟩
  initial_lift := by
    rintro (v | (v | v)) hv
    · exact ⟨.inl (.inl v), hv, rfl⟩
    · exact ⟨.inl (.inr v), hv, rfl⟩
    · exact ⟨.inr v, hv, rfl⟩
  root_lift := by
    rintro (v | (v | v)) hv
    · exact ⟨.inl (.inl v), hv, rfl⟩
    · exact ⟨.inl (.inr v), hv, rfl⟩
    · exact ⟨.inr v, hv, rfl⟩
  edge_lift := by
    rintro ((v | v) | v) d t ht
    · obtain ⟨r, hr, rfl⟩ := ht
      refine ⟨Sum.map Sum.inl id (Sum.map Sum.inl id r), ⟨_, ⟨r, hr, rfl⟩, rfl⟩, ?_⟩
      cases r <;> rfl
    · obtain ⟨s, ⟨r, hr, rfl⟩, rfl⟩ := ht
      refine ⟨Sum.map Sum.inl id (Sum.map Sum.inr id r), ⟨_, ⟨r, hr, rfl⟩, rfl⟩, ?_⟩
      cases r <;> rfl
    · obtain ⟨s, ⟨r, hr, rfl⟩, rfl⟩ := ht
      refine ⟨Sum.map Sum.inr id r, ⟨r, hr, rfl⟩, ?_⟩
      cases r <;> rfl

noncomputable def swap {A : RankedSet} {n : ℕ} {V W : Type}
    (S : Presentation A n V) (T : Presentation A n W) : Cover (combine S T) (combine T S) where
  toFun := Sum.swap
  label := by intro v; cases v <;> rfl
  initial := by intro v h; cases v <;> exact h
  root := by intro v h; cases v <;> exact h
  edge := by
    intro v d t ht
    cases v <;> obtain ⟨s, hs, rfl⟩ := ht <;> exact ⟨s, hs, by cases s <;> rfl⟩
  initial_lift := by
    intro v h
    refine ⟨Sum.swap v, ?_, by cases v <;> rfl⟩
    cases v <;> exact h
  root_lift := by
    intro v h
    refine ⟨Sum.swap v, ?_, by cases v <;> rfl⟩
    cases v <;> exact h
  edge_lift := by
    intro v d t ht
    cases v with
    | inl v =>
      obtain ⟨s, hs, rfl⟩ := ht
      exact ⟨Sum.map Sum.inl id s, ⟨s, hs, rfl⟩, by cases s <;> rfl⟩
    | inr v =>
      obtain ⟨s, hs, rfl⟩ := ht
      exact ⟨Sum.map Sum.inr id s, ⟨s, hs, rfl⟩, by cases s <;> rfl⟩

end Lax369799Proofs.SumCovers
