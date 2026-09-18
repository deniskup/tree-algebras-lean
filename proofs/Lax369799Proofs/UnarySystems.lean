import Lax369799.UnarySystems
import Lax369799Proofs.PresentationObservations

namespace Lax369799Proofs.UnarySystems
open Lax369799.RankedSystems Lax369799.Morphisms Lax369799.UnarySystems
open Lax369799Proofs.Pullbacks

private theorem successor_unique {A : RankedSet} {n : ℕ} (S : System A n)
    (hS : ∀ v, (S.val.graph.label v).1 ≤ 1) {v : S.val.Vertex}
    {d e : ℕ} {t u : S.val.Vertex ⊕ Fin n}
    (ht : S.val.graph.edge v d t) (hu : S.val.graph.edge v e u) : t = u := by
  have hd := S.val.graph.direction_valid v d t ht
  have he := S.val.graph.direction_valid v e u hu
  have hv := hS v
  have hde : d = e := by omega
  subst e
  exact (S.property.2.2 v d hd).unique ht hu

private theorem path_comparable {A : RankedSet} {n : ℕ} (S : System A n)
    (hS : ∀ v, (S.val.graph.label v).1 ≤ 1) (v w : S.val.Vertex) :
    Relation.ReflTransGen S.val.graph.Step v w ∨ Relation.ReflTransGen S.val.graph.Step w v := by
  obtain ⟨r, hr⟩ := S.property.1
  have path (v : S.val.Vertex) : Relation.ReflTransGen S.val.graph.Step r v := by
    obtain ⟨s, hs, hp⟩ := S.val.reachable v
    rcases hs with hs | hs
    · rw [hr] at hs
      exact hs ▸ hp
    · rw [S.property.2.1] at hs
      exact False.elim hs
  apply Relation.ReflTransGen.total_of_right_unique ?_ (path v) (path w)
  rintro a b c ⟨d, hd⟩ ⟨e, he⟩
  exact Sum.inl.inj (successor_unique S hS hd he)

private theorem path_from_exit {A : RankedSet} {n : ℕ} (S : System A n)
    (hS : ∀ v, (S.val.graph.label v).1 ≤ 1) {v w : S.val.Vertex} {d : ℕ} {i : Fin n}
    (hi : S.val.graph.edge v d (.inr i)) (hp : Relation.ReflTransGen S.val.graph.Step v w) :
    v = w := by
  rcases hp.cases_head with he | ⟨z, ⟨e, hz⟩, _⟩
  · exact he
  · have he := successor_unique S hS hi hz
    cases he

/--
---
conclusion: Lax369799.UnarySystems.unique_exit
---
All vertices lie on a single path from the initial vertex. An exit vertex
has no internal successor, so any two exit vertices coincide; uniqueness
of the deterministic successor then identifies their variables.
-/
theorem unique_exit {A : RankedSet} {n : ℕ} (S : System A n)
    (hS : ∀ v, (S.val.graph.label v).1 ≤ 1)
    {v w : S.val.Vertex} {d e : ℕ} {i j : Fin n}
    (hi : S.val.graph.edge v d (.inr i)) (hj : S.val.graph.edge w e (.inr j)) : i = j := by
  have hvw : v = w := (path_comparable S hS v w).elim
    (path_from_exit S hS hi) (fun h => (path_from_exit S hS hj h).symm)
  subst w
  exact Sum.inr.inj (successor_unique S hS hi hj)

private def forget {A : RankedSet} {n : ℕ} {V : Type} (G : Presentation A n V) :
    Map (variablePieces G) G where
  toFun := Prod.snd
  label := fun _ => rfl
  initial := fun _ h => h
  root := fun _ h => h
  edge := by
    rintro v d t ⟨s, hs, _, rfl⟩
    cases s <;> exact hs

private theorem lift_piece {A : RankedSet} {n : ℕ} (hn : 0 < n) {V : Type}
    (G : Presentation A n V) (hG : ∀ v, (G.label v).1 ≤ 1)
    (D : System A n) (f : Map D.val.graph G) : Nonempty (Map D.val.graph (variablePieces G)) := by
  classical
  have hD (v : D.val.Vertex) : (D.val.graph.label v).1 ≤ 1 := by
    rw [← f.label v]
    exact hG _
  have chosen : ∃ i : Fin n, ∀ v d j, D.val.graph.edge v d (.inr j) → j = i := by
    by_cases he : ∃ v d j, D.val.graph.edge v d (.inr j)
    · obtain ⟨v, d, i, hi⟩ := he
      exact ⟨i, fun _ _ _ hj => unique_exit D hD hj hi⟩
    · exact ⟨⟨0, hn⟩, fun v d j hj => False.elim (he ⟨v, d, j, hj⟩)⟩
  obtain ⟨i, hi⟩ := chosen
  refine ⟨{
    toFun := fun v => (i, f.toFun v)
    label := f.label
    initial := f.initial
    root := f.root
    edge := ?_ }⟩
  intro v d t ht
  refine ⟨Sum.map f.toFun id t, f.edge v d t ht, ?_, ?_⟩
  · intro j hj
    cases t with
    | inl w => cases hj
    | inr k => exact (Sum.inr.inj hj).symm.trans (hi v d k ht)
  · cases t <;> rfl

private theorem initial_pieces {A : RankedSet} {n : ℕ} (hn : 0 < n)
    {V : Type} [Fintype V] (G : Presentation A n V) (hG : ∀ v, (G.label v).1 ≤ 1)
    (U : System A n) : InitYield (trim G) U ↔ InitYield (trim (variablePieces G)) U := by
  constructor
  · rintro ⟨D, ⟨d⟩, hd⟩
    obtain ⟨f⟩ := lift_piece hn G hG D (PresentationObservations.toPresentation d)
    exact ⟨D, ⟨lift f⟩, hd⟩
  · exact Yields.initial_yield_forward (trimMap (forget G))

private theorem root_trim {A : RankedSet} {n : ℕ} {V : Type} [Fintype V]
    (G : Presentation A n V) (U : System A n) :
    InitYield (uproot (trim G)) U ↔ InitYield (trim (Lax369799.RootExpansion.startAtRoots G)) U := by
  let f := PresentationObservations.rootedCover (FiniteAcceptance.trimProjection G)
  let g : Map _ _ := ⟨f.toFun, f.initial, f.root, f.label, f.edge⟩
  exact ⟨Yields.initial_yield_forward (trimMap g),
    Yields.initial_yield_backward (trimMap g)
      (trimMap_surjective g f.initial_lift f.root_lift f.edge_lift)⟩

/--
---
conclusion: Lax369799.UnarySystems.variable_decomposition
---
Every deterministic resolution uses at most one variable, so it lifts to
that variable's copy. If it has no exit, choose any copy. Forgetting the
copy index gives the converse, for initial and root resolutions alike.
-/
theorem variable_decomposition {A : RankedSet} {n : ℕ} (hn : 0 < n)
    {V : Type} [Fintype V] (G : Presentation A n V)
    (hG : ∀ v, (G.label v).1 ≤ 1) :
    YieldEquivalent (trim G) (trim (variablePieces G)) := by
  intro W
  have hi := initial_pieces hn G hG
  have hr (U : System A n) : InitYield (uproot (trim G)) U ↔
      InitYield (uproot (trim (variablePieces G))) U := by
    rw [root_trim, root_trim]
    exact initial_pieces hn (Lax369799.RootExpansion.startAtRoots G) hG U
  constructor
  · rintro (⟨U, hu, rfl⟩ | ⟨U, hu, rfl⟩)
    · exact Or.inl ⟨U, (hi U).mp hu, rfl⟩
    · exact Or.inr ⟨U, (hr U).mp hu, rfl⟩
  · rintro (⟨U, hu, rfl⟩ | ⟨U, hu, rfl⟩)
    · exact Or.inl ⟨U, (hi U).mpr hu, rfl⟩
    · exact Or.inr ⟨U, (hr U).mpr hu, rfl⟩

end Lax369799Proofs.UnarySystems
