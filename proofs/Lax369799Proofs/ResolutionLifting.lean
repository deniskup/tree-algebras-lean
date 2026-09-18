import Lax369799.ResolutionLifting
import Lax369799Proofs.MorphismTheorems

set_option backward.isDefEq.respectTransparency false
namespace Lax369799Proofs.ResolutionLifting
open Lax369799.RankedSystems Lax369799.Morphisms Lax369799.Resolutions

private def graph {A : RankedSet} {m n : ℕ} (σ : Fin m → Fin n)
    (S : System A m) (R : System A n) (f : Morphism R.val (rename σ S.val)) :
    Presentation A m R.val.Vertex where
  label := R.val.graph.label
  initial := R.val.graph.initial
  root := R.val.graph.root
  edge := fun v d t => R.val.graph.edge v d (Sum.map id σ t) ∧
    S.val.graph.edge (f.toFun v) d (Sum.map f.toFun id t)
  direction_valid := fun v d _t h => R.val.graph.direction_valid v d _ h.1

private theorem edge_lift {A : RankedSet} {m n : ℕ} (σ : Fin m → Fin n)
    (S : System A m) (R : System A n) (f : Morphism R.val (rename σ S.val))
    (v : R.val.Vertex) (d : ℕ) (t : R.val.Vertex ⊕ Fin n) (ht : R.val.graph.edge v d t) :
    ∃ s, (graph σ S R f).edge v d s ∧ Sum.map id σ s = t := by
  obtain ⟨u, hu, he⟩ := f.edge v d t ht
  cases t with
  | inl w =>
    cases u with
    | inl z =>
      have hz : f.toFun w = z := Sum.inl.inj he
      refine ⟨.inl w, ⟨ht, ?_⟩, rfl⟩
      change S.val.graph.edge (f.toFun v) d (.inl (f.toFun w))
      rw [hz]
      exact hu
    | inr i => cases he
  | inr j =>
    cases u with
    | inl z => cases he
    | inr i =>
      have hj : j = σ i := Sum.inr.inj he
      refine ⟨.inr i, ⟨?_, hu⟩, ?_⟩
      · change R.val.graph.edge v d (.inr (σ i))
        rw [← hj]
        exact ht
      · exact congrArg Sum.inr hj.symm

private theorem internal {A : RankedSet} {m n : ℕ} (σ : Fin m → Fin n)
    (S : System A m) (R : System A n) (f : Morphism R.val (rename σ S.val))
    {v w : R.val.Vertex} {d : ℕ} (ht : R.val.graph.edge v d (.inl w)) :
    (graph σ S R f).edge v d (.inl w) := by
  obtain ⟨s, hs, he⟩ := edge_lift σ S R f v d (.inl w) ht
  cases s with
  | inl z => cases Sum.inl.inj he; exact hs
  | inr i => cases he

private def system {A : RankedSet} {m n : ℕ} (σ : Fin m → Fin n)
    (S : System A m) (R : System A n) (f : Morphism R.val (rename σ S.val)) : System A m := by
  refine ⟨{ size := R.val.size, graph := graph σ S R f, reachable := ?_ },
    R.property.1, R.property.2.1, ?_⟩
  · intro v
    obtain ⟨r, hr, hp⟩ := R.val.reachable v
    refine ⟨r, hr, Relation.ReflTransGen.mono ?_ r v hp⟩
    rintro a b ⟨d, hd⟩
    exact ⟨d, internal σ S R f hd⟩
  · intro v d hd
    obtain ⟨t, ht, _⟩ := R.property.2.2 v d hd
    obtain ⟨s, hs, _⟩ := edge_lift σ S R f v d t ht
    refine ⟨s, hs, ?_⟩
    intro u hu
    have hR := (R.property.2.2 v d hd).unique hu.1 hs.1
    have hl : S.val.graph.label (f.toFun v) = R.val.graph.label v := f.label v
    have hdir : d < (S.val.graph.label (f.toFun v)).1 := by
      rw [hl]
      exact hd
    have hS := (S.property.2.2 (f.toFun v) d hdir).unique hu.2 hs.2
    cases u with
    | inl u =>
      cases s with
      | inl s => exact congrArg Sum.inl (Sum.inl.inj hR)
      | inr j => cases hR
    | inr i =>
      cases s with
      | inl s => cases hR
      | inr j => exact congrArg Sum.inr (Sum.inr.inj hS)

private theorem renamed {A : RankedSet} {m n : ℕ} (σ : Fin m → Fin n)
    (S : System A m) (R : System A n) (f : Morphism R.val (rename σ S.val)) :
    rename σ (system σ S R f).val = R.val := by
  have he : (rename σ (system σ S R f).val).graph.edge = R.val.graph.edge := by
    funext v d t
    apply propext
    constructor
    · rintro ⟨s, hs, rfl⟩
      exact hs.1
    · intro ht
      obtain ⟨s, hs, he⟩ := edge_lift σ S R f v d t ht
      exact ⟨s, hs, he.symm⟩
  cases R with
  | mk R hr =>
    cases R with
    | mk size G hreach =>
      cases G
      dsimp only [rename, system, graph] at he ⊢
      congr 1
      congr 1

/--
---
conclusion: Lax369799.ResolutionLifting.rename_lift
---
Keep the source vertices and internal edges. For each variable edge,
restore the variable selected by the unique successor in the original
unrenamed target. The two deterministic edge conditions ensure uniqueness.
-/
theorem rename_lift {A : RankedSet} {m n : ℕ} (σ : Fin m → Fin n)
    (S : System A m) (R : System A n) (f : Morphism R.val (rename σ S.val)) :
    ∃ U : System A m, rename σ U.val = R.val ∧ UnfoldsTo S.val U.val := by
  let U := system σ S R f
  let g : Morphism U.val S.val := {
    toFun := f.toFun
    initial := f.initial
    root := f.root
    label := f.label
    edge := fun _ _ _ h => h.2 }
  exact ⟨U, renamed σ S R f,
    ⟨g, MorphismTheorems.system_morphism_locally_surjective U S g⟩⟩

theorem initial_mono {A : RankedSet} {n : ℕ} {S S' : SetSystem A n}
    (h : YieldBelow S S') (R : System A n) (hy : InitYield S R) : InitYield S' R := by
  rcases h R.val (Or.inl ⟨R, hy, rfl⟩) with ⟨U, hU, he⟩ | ⟨U, _, he⟩
  · have he' : R = U := Subtype.ext he
    exact he'.symm ▸ hU
  · obtain ⟨i, hi⟩ := R.property.1
    have hempty : R.val.graph.initial = ∅ := by rw [he]; rfl
    have hh : i ∈ R.val.graph.initial := by rw [hi]; rfl
    rw [hempty] at hh
    exact False.elim hh

theorem transfer_initial {A : RankedSet} {m n : ℕ} {S S' : SetSystem A n}
    (h : ∀ R, InitYield S R → InitYield S' R) (T : System A m) (σ : Fin m → Fin n)
    (hT : IsResolution S T σ) :
    ∃ T' : System A m, IsResolution S' T' σ ∧ UnfoldsTo T.val T'.val := by
  let R := Lax369799.Renaming.renameSystem σ T
  have hy : InitYield S R := ⟨R, hT,
    ⟨MorphismTheorems.identity R.val, MorphismTheorems.identity_surjective R.val⟩⟩
  obtain ⟨D, hD, f, _⟩ := h R hy
  obtain ⟨T', he, ht⟩ := rename_lift σ T D f
  refine ⟨T', ?_, ht⟩
  change Nonempty (Morphism (rename σ T'.val) S')
  rw [he]
  exact hD

/--
---
conclusion: Lax369799.ResolutionLifting.transfer
---
Apply yield inclusion to the renamed system, then lift the resulting
unfolding through its variable renaming (Section 2.9).
-/
theorem transfer {A : RankedSet} {m n : ℕ} {S S' : SetSystem A n}
    (h : YieldBelow S S') (T : System A m) (σ : Fin m → Fin n)
    (hT : IsResolution S T σ) :
    ∃ T' : System A m, IsResolution S' T' σ ∧ UnfoldsTo T.val T'.val :=
  transfer_initial (initial_mono h) T σ hT

end Lax369799Proofs.ResolutionLifting
