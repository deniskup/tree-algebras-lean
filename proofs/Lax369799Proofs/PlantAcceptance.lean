import Lax369799Proofs.Acceptance

namespace Lax369799Proofs.PlantAcceptance
open Lax369799.RankedSystems Lax369799.Morphisms Lax369799.Algebras
open Lax369799.SyntacticOrder
open Lax369799Proofs.Pullbacks

private def reroot {A : RankedSet} {n : ℕ} (S : SetSystem A n) : SetSystem A n where
  size := S.size
  graph := { S.graph with initial := S.graph.root ∪ S.graph.initial, root := ∅ }
  reachable := by
    intro v
    obtain ⟨r, hr, hp⟩ := S.reachable v
    exact ⟨r, Or.inl (hr.elim Or.inr Or.inl), hp⟩

private theorem reroot_plant {A : RankedSet} {n : ℕ} (S : System A n) :
    reroot (plant S.val) = S.val := by
  obtain ⟨⟨size, G, hr⟩, hs⟩ := S
  obtain ⟨label, initial, root, edge, valid⟩ := G
  have he := hs.2.1
  change root = ∅ at he
  subst root
  simp only [reroot, plant, Set.empty_union]
  congr 1
  congr 1
  exact Set.union_empty initial

private theorem plant_injective {A : RankedSet} {n : ℕ} (S T : System A n)
    (h : plant S.val = plant T.val) : S = T := by
  apply Subtype.ext
  have hh := congrArg reroot h
  rw [reroot_plant, reroot_plant] at hh
  exact hh

private theorem no_initial_plant {A : RankedSet} {n : ℕ} (S : SetSystem A n)
    (U : System A n) : ¬ InitYield (plant S) U := by
  rintro ⟨D, ⟨d⟩, _⟩
  obtain ⟨i, hi⟩ := D.property.1
  exact d.initial i (by rw [hi]; rfl)

private theorem root_yield_plant {A : RankedSet} {n : ℕ} (S : SetSystem A n)
    (U : System A n) :
    InitYield (uproot (plant S)) U ↔ InitYield S U ∨ InitYield (uproot S) U := by
  constructor
  · rintro ⟨D, ⟨d⟩, hd⟩
    obtain ⟨i, hi⟩ := D.property.1
    let G : Presentation A n S.Vertex :=
      { (plant S).graph with initial := (plant S).graph.root, root := ∅ }
    let f := fun v => vertex G (d.toFun v)
    have hm : S.graph.root (f i) ∨ S.graph.initial (f i) := d.initial i (by rw [hi]; rfl)
    have edge : ∀ v k t, D.val.graph.edge v k t → S.graph.edge (f v) k (Sum.map f id t) := by
      intro v k t ht
      have hh := d.edge v k t ht
      cases t <;> exact hh
    rcases hm with hm | hm
    · right
      refine ⟨D, ⟨lift (T := { S.graph with initial := S.graph.root, root := ∅ }) {
        toFun := f
        initial := ?_
        root := ?_
        label := d.label
        edge := edge }⟩, hd⟩
      · intro v hv
        rw [hi] at hv
        exact hv ▸ hm
      · intro v hv
        rw [D.property.2.1] at hv
        exact hv
    · left
      refine ⟨D, ⟨{ toFun := f, initial := ?_, root := ?_, label := d.label, edge := edge }⟩, hd⟩
      · intro v hv
        rw [hi] at hv
        exact hv ▸ hm
      · intro v hv
        rw [D.property.2.1] at hv
        exact False.elim hv
  · rintro (⟨D, ⟨d⟩, hd⟩ | ⟨D, ⟨d⟩, hd⟩)
    · refine ⟨D, ⟨lift (T := { (plant S).graph with initial := (plant S).graph.root, root := ∅ }) {
        toFun := d.toFun
        initial := fun v hv => Or.inr (d.initial v hv)
        root := ?_
        label := d.label
        edge := d.edge }⟩, hd⟩
      intro v hv
      rw [D.property.2.1] at hv
      exact hv
    · let G : Presentation A n S.Vertex := { S.graph with initial := S.graph.root, root := ∅ }
      refine ⟨D, ⟨lift (T := { (plant S).graph with initial := (plant S).graph.root, root := ∅ }) {
        toFun := fun v => vertex G (d.toFun v)
        initial := fun v hv => Or.inl (d.initial v hv)
        root := ?_
        label := d.label
        edge := ?_ }⟩, hd⟩
      · intro v hv
        rw [D.property.2.1] at hv
        exact hv
      · intro v k t ht
        have hh := d.edge v k t ht
        cases t <;> exact hh

private theorem system_ne_plant {A : RankedSet} {n : ℕ} (S T : System A n) :
    S.val ≠ plant T.val := by
  intro h
  obtain ⟨i, hi⟩ := S.property.1
  have he : S.val.graph.initial = ∅ := by rw [h]; rfl
  have hh : i ∈ S.val.graph.initial := by rw [hi]; rfl
  rw [he] at hh
  exact hh

theorem accepting_iff {A : RankedSet} (L : Language A) (S : SetSystem A 0) :
    Accepting L S ↔ ∀ U, InitYield S U ∨ InitYield (uproot S) U → U ∈ L := by
  constructor
  · intro h U hu
    rcases hu with hu | hu
    · obtain ⟨V, hv, he⟩ := h U.val (Or.inl ⟨U, hu, rfl⟩)
      rcases he with he | he
      · exact (Subtype.ext he : U = V) ▸ hv
      · exact False.elim (system_ne_plant U V he)
    · obtain ⟨V, hv, he⟩ := h (plant U.val) (Or.inr ⟨U, hu, rfl⟩)
      rcases he with he | he
      · exact False.elim (system_ne_plant V U he.symm)
      · exact (plant_injective U V he) ▸ hv
  · intro h T ht
    rcases ht with ⟨U, hu, rfl⟩ | ⟨U, hu, rfl⟩
    · exact ⟨U, h U (Or.inl hu), Or.inl rfl⟩
    · exact ⟨U, h U (Or.inr hu), Or.inr rfl⟩

/--
---
conclusion: Lax369799.AcceptanceTheorems.accepting_plant
---
Planting turns initial yields into root yields and retains all existing
root yields. Universal language acceptance is therefore unchanged.
-/
theorem accepting_plant {A : RankedSet} (L : Language A) (S : SetSystem A 0) :
    Accepting L (plant S) ↔ Accepting L S := by
  rw [accepting_iff, accepting_iff]
  constructor
  · intro h U hu
    exact h U (Or.inr ((root_yield_plant S U).mpr hu))
  · intro h U hu
    rcases hu with hu | hu
    · exact False.elim (no_initial_plant S U hu)
    · exact h U ((root_yield_plant S U).mp hu)

end Lax369799Proofs.PlantAcceptance
