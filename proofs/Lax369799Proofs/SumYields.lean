import Lax369799Proofs.Acceptance

namespace Lax369799Proofs.SumYields
open Lax369799.RankedSystems Lax369799.Morphisms
open Lax369799Proofs.Pullbacks Lax369799Proofs.SumCovers

private theorem side_edge {A : RankedSet} {n : ℕ} {V W : Type}
    (G : Presentation A n V) (H : Presentation A n W) (v w : V ⊕ W)
    (d : ℕ) (h : (combine G H).edge v d (.inl w)) : v.isLeft = w.isLeft := by
  cases v <;> obtain ⟨s, _, hs⟩ := h <;> cases s with
  | inl u => cases Sum.inl.inj hs; rfl
  | inr i => cases hs

private theorem same_side {A : RankedSet} {n : ℕ} {V W : Type}
    (D : System A n) (G : Presentation A n V) (H : Presentation A n W)
    (f : Map D.val.graph (combine G H)) :
    ∀ v w, (f.toFun v).isLeft = (f.toFun w).isLeft := by
  obtain ⟨r, hr⟩ := D.property.1
  have all (v : D.val.Vertex) : (f.toFun r).isLeft = (f.toFun v).isLeft := by
    obtain ⟨s, hs, hp⟩ := D.val.reachable v
    rcases hs with hs | hs
    · rw [hr] at hs
      have hs : s = r := hs
      subst s
      induction hp with
      | refl => rfl
      | @tail b c hp he ih =>
        obtain ⟨d, hd⟩ := he
        exact ih.trans (side_edge G H _ _ d (f.edge b d (.inl c) hd))
    · rw [D.property.2.1] at hs
      exact False.elim hs
  exact fun v w => (all v).symm.trans (all w)

private noncomputable def factorLeft {A : RankedSet} {n : ℕ} {V W : Type}
    (D : System A n) (G : Presentation A n V) (H : Presentation A n W)
    (f : Map D.val.graph (combine G H))
    (hf : ∀ v, ∃ w, f.toFun v = .inl w) : Map D.val.graph G := by
  classical
  let g := fun v => Classical.choose (hf v)
  have hg v : f.toFun v = .inl (g v) := Classical.choose_spec (hf v)
  exact {
    toFun := g
    label := by
      intro v
      have h := f.label v
      rw [hg v] at h
      exact h
    initial := by
      intro v hv
      have h := f.initial v hv
      rw [hg v] at h
      exact h
    root := by intro v hv; rw [D.property.2.1] at hv; exact False.elim hv
    edge := by
      intro v d t ht
      have h := f.edge v d t ht
      rw [hg v] at h
      obtain ⟨s, hs, he⟩ := h
      cases t with
      | inl w =>
        simp only [Sum.map_inl] at he
        rw [hg w] at he
        cases s with
        | inl u =>
          have hu := Sum.inl.inj (Sum.inl.inj he)
          change G.edge (g v) d (.inl (g w))
          rw [hu]
          exact hs
        | inr i => cases he
      | inr i =>
        cases s with
        | inl u => cases he
        | inr j =>
          have hij : i = j := Sum.inr.inj he
          change G.edge (g v) d (.inr i)
          rw [hij]
          exact hs }

private theorem factor {A : RankedSet} {n : ℕ} {V W : Type}
    (D : System A n) (G : Presentation A n V) (H : Presentation A n W)
    (f : Map D.val.graph (combine G H)) :
    Nonempty (Map D.val.graph G) ∨ Nonempty (Map D.val.graph H) := by
  classical
  obtain ⟨r, _⟩ := D.property.1
  cases he : f.toFun r with
  | inl u =>
    apply Or.inl
    apply Nonempty.intro
    apply factorLeft D G H f
    intro v
    have hv := same_side D G H f r v
    rw [he] at hv
    cases hv' : f.toFun v with
    | inl w => exact ⟨w, rfl⟩
    | inr w => rw [hv'] at hv; cases hv
  | inr u =>
    let sf : Map D.val.graph (combine H G) := {
      toFun := fun v => (f.toFun v).swap
      initial := fun v hv => (swap G H).initial _ (f.initial v hv)
      root := fun v hv => (swap G H).root _ (f.root v hv)
      label := fun v => ((swap G H).label _).trans (f.label v)
      edge := by
        intro v d t ht
        have h := (swap G H).edge _ d _ (f.edge v d t ht)
        cases t <;> exact h }
    apply Or.inr
    apply Nonempty.intro
    apply factorLeft D H G sf
    intro v
    have hv := same_side D G H f r v
    rw [he] at hv
    cases hv' : f.toFun v with
    | inl w => rw [hv'] at hv; cases hv
    | inr w => exact ⟨w, by change (f.toFun v).swap = _; rw [hv']; rfl⟩

private def rootGraph {A : RankedSet} {n : ℕ} {V : Type}
    (G : Presentation A n V) : Presentation A n V :=
  { G with initial := G.root, root := ∅ }

private theorem root_edge_iff {A : RankedSet} {n : ℕ} (S T : SetSystem A n)
    (v : S.Vertex ⊕ T.Vertex) (d : ℕ) (t : (S.Vertex ⊕ T.Vertex) ⊕ Fin n) :
    (SumEvaluation.sumGraph S T).edge v d t ↔
      (combine (rootGraph S.graph) (rootGraph T.graph)).edge v d t := by
  cases v <;> rfl

private theorem sum_edge_iff {A : RankedSet} {n : ℕ} (S T : SetSystem A n)
    (v : S.Vertex ⊕ T.Vertex) (d : ℕ) (t : (S.Vertex ⊕ T.Vertex) ⊕ Fin n) :
    (SumEvaluation.sumGraph S T).edge v d t ↔ (combine S.graph T.graph).edge v d t := by
  cases v <;> rfl

private noncomputable def rootSumProjection {A : RankedSet} {n : ℕ}
    (S T : SetSystem A n) :
    Map (uproot (sum S T)).graph (combine (rootGraph S.graph) (rootGraph T.graph)) where
  toFun := fun v => vertex (SumEvaluation.sumGraph S T)
    (vertex (rootGraph (sum S T).graph) v)
  label := by intro v; rfl
  initial := by
    intro v hv
    exact hv
  root := fun _ h => False.elim h
  edge := by
    intro v d t ht
    apply (root_edge_iff S T _ d _).mp
    cases t <;> exact ht

private noncomputable def sumProjection {A : RankedSet} {n : ℕ}
    (S T : SetSystem A n) : Map (sum S T).graph (combine S.graph T.graph) where
  toFun := vertex (SumEvaluation.sumGraph S T)
  label := fun _ => rfl
  initial := fun _ h => h
  root := fun _ h => h
  edge := by
    intro v d t h
    exact (sum_edge_iff S T _ d _).mp h

private def precompose {A : RankedSet} {n : ℕ} {V : Type}
    {S T : SetSystem A n} {G : Presentation A n V}
    (f : Morphism S T) (g : Map T.graph G) : Map S.graph G where
  toFun := g.toFun ∘ f.toFun
  initial := fun v hv => g.initial _ (f.initial v hv)
  root := fun v hv => g.root _ (f.root v hv)
  label := fun v => (g.label _).trans (f.label v)
  edge := by
    intro v d t h
    have he := g.edge _ d _ (f.edge v d t h)
    cases t <;> exact he

private theorem initial_split {A : RankedSet} {n : ℕ}
    (S T : SetSystem A n) (U : System A n) (h : InitYield (sum S T) U) :
    InitYield S U ∨ InitYield T U := by
  obtain ⟨D, ⟨d⟩, hu⟩ := h
  rcases factor D S.graph T.graph (precompose d (sumProjection S T)) with hf | hf
  · obtain ⟨f⟩ := hf
    exact Or.inl ⟨D, ⟨⟨f.toFun, f.initial, f.root, f.label, f.edge⟩⟩, hu⟩
  · obtain ⟨f⟩ := hf
    exact Or.inr ⟨D, ⟨⟨f.toFun, f.initial, f.root, f.label, f.edge⟩⟩, hu⟩

private theorem root_split {A : RankedSet} {n : ℕ}
    (S T : SetSystem A n) (U : System A n) (h : InitYield (uproot (sum S T)) U) :
    InitYield (uproot S) U ∨ InitYield (uproot T) U := by
  obtain ⟨D, ⟨d⟩, hu⟩ := h
  rcases factor D (rootGraph S.graph) (rootGraph T.graph)
    (precompose d (rootSumProjection S T)) with hf | hf
  · obtain ⟨f⟩ := hf
    exact Or.inl ⟨D, ⟨lift f⟩, hu⟩
  · obtain ⟨f⟩ := hf
    exact Or.inr ⟨D, ⟨lift f⟩, hu⟩

private noncomputable def includeLeft {A : RankedSet} {n : ℕ} (S T : SetSystem A n) :
    Morphism S (sum S T) := lift (T := SumEvaluation.sumGraph S T) {
      toFun := Sum.inl
      label := fun _ => rfl
      initial := fun _ h => h
      root := fun _ h => h
      edge := fun _ _ t h => ⟨t, h, rfl⟩ }

private noncomputable def includeRight {A : RankedSet} {n : ℕ} (S T : SetSystem A n) :
    Morphism T (sum S T) := lift (T := SumEvaluation.sumGraph S T) {
      toFun := Sum.inr
      label := fun _ => rfl
      initial := fun _ h => h
      root := fun _ h => h
      edge := fun _ _ t h => ⟨t, h, rfl⟩ }

/--
---
conclusion: Lax369799.AcceptanceTheorems.yield_sum
---
A deterministic resolution starts in one summand and all its reachable
vertices stay there. Apply this to initial and root resolutions. The
converse follows from the two inclusion morphisms.
-/
theorem yield_sum {A : RankedSet} {n : ℕ} (S T U : SetSystem A n) :
    Yield (sum S T) U ↔ Yield S U ∨ Yield T U := by
  constructor
  · rintro (⟨V, hv, rfl⟩ | ⟨V, hv, rfl⟩)
    · rcases initial_split S T V hv with h | h
      · exact Or.inl (Or.inl ⟨V, h, rfl⟩)
      · exact Or.inr (Or.inl ⟨V, h, rfl⟩)
    · rcases root_split S T V hv with h | h
      · exact Or.inl (Or.inr ⟨V, h, rfl⟩)
      · exact Or.inr (Or.inr ⟨V, h, rfl⟩)
  · rintro (h | h)
    · exact (Yields.morphism_yields (includeLeft S T)).1 U h
    · exact (Yields.morphism_yields (includeRight S T)).1 U h

/--
---
conclusion: Lax369799.AcceptanceTheorems.accepting_sum
---
Universal acceptance of the union of the two sets of yields is equivalent
to universal acceptance of each of them.
-/
theorem accepting_sum {A : RankedSet} (L : Lax369799.Algebras.Language A)
    (S T : SetSystem A 0) :
    Lax369799.SyntacticOrder.Accepting L (sum S T) ↔
      Lax369799.SyntacticOrder.Accepting L S ∧ Lax369799.SyntacticOrder.Accepting L T := by
  constructor
  · intro h
    exact ⟨fun U hu => h U ((yield_sum S T U).mpr (Or.inl hu)),
      fun U hu => h U ((yield_sum S T U).mpr (Or.inr hu))⟩
  · rintro ⟨hs, ht⟩ U hu
    exact ((yield_sum S T U).mp hu).elim (hs U) (ht U)

end Lax369799Proofs.SumYields
