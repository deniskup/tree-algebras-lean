import Lax369799.SupportPorts
import Lax369799Proofs.RawSystemFlattening
import Lax369799Proofs.UntrimmedFlattening

namespace Lax369799Proofs.SupportPorts
set_option backward.isDefEq.respectTransparency false
open Lax369799
open RankedSystems FinitePresentations Lax369799.SupportPorts
open Lax369799Proofs.DeterministicNormalForms

private theorem rename_internal {B : RankedSet} {a b : ℕ} (σ : Fin a → Fin b)
    (S : System B a) (v w : S.val.Vertex) (d : ℕ) :
    (Renaming.renameSystem σ S).val.graph.edge v d (.inl w) ↔ S.val.graph.edge v d (.inl w) := by
  constructor
  · rintro ⟨t, ht, he⟩
    cases t with
    | inl u => cases he; exact ht
    | inr i => cases he
  · intro h
    exact ⟨.inl w, h, rfl⟩

private theorem rename_variable {B : RankedSet} {a b : ℕ} (σ : Fin a → Fin b)
    (S : System B a) (v : S.val.Vertex) (d : ℕ) (j : Fin b) :
    (Renaming.renameSystem σ S).val.graph.edge v d (.inr j) ↔
      ∃ i, S.val.graph.edge v d (.inr i) ∧ j = σ i := by
  constructor
  · rintro ⟨t, ht, he⟩
    cases t with
    | inl u => cases he
    | inr i => exact ⟨i, ht, Sum.inr.inj he⟩
  · rintro ⟨i, hi, rfl⟩
    exact ⟨.inr i, hi, rfl⟩

variable {A B : RankedSet} {n : ℕ} {V : Type}
    (G : Presentation A n V) (m : V → ℕ)
    (σ : ∀ v, Fin (m v) → Fin (G.label v).1) (S : ∀ v, System B (m v))

private theorem expanded_internal (v w : (x : V) × (S x).val.Vertex) (d : ℕ) :
    (rawFlatten (expanded G m σ S)).edge v d (.inl w) ↔
      (∃ z, (S v.1).val.graph.edge v.2 d (.inl z) ∧ w = ⟨v.1,z⟩) ∨
      (∃ i, (S v.1).val.graph.edge v.2 d (.inr i) ∧
        G.edge v.1 (σ v.1 i).val (.inl w.1) ∧ (S w.1).val.graph.initial w.2) := by
  change ((∃ z, (Renaming.renameSystem (σ v.1) (S v.1)).val.graph.edge v.2 d (.inl z) ∧
    Sum.inl w = Sum.inl ⟨v.1,z⟩) ∨
    ∃ i, (Renaming.renameSystem (σ v.1) (S v.1)).val.graph.edge v.2 d (.inr i) ∧
      ((∃ u, G.edge v.1 i.val (.inl u.1) ∧ (S u.1).val.graph.initial u.2 ∧
        Sum.inl w = Sum.inl u) ∨ (∃ j, G.edge v.1 i.val (.inr j) ∧ Sum.inl w = Sum.inr j))) ↔ _
  simp only [rename_internal, rename_variable, Sum.inl.injEq, reduceCtorEq, and_false,
    exists_false, or_false]
  constructor
  · rintro (h | ⟨i, ⟨j, hj, rfl⟩, u, hu, hi, rfl⟩)
    · exact Or.inl h
    · exact Or.inr ⟨j, hj, hu, hi⟩
  · rintro (h | ⟨i, hi, he, hmark⟩)
    · exact Or.inl h
    · exact Or.inr ⟨σ v.1 i, ⟨i, hi, rfl⟩, w, he, hmark, rfl⟩

private theorem restricted_internal (v w : (x : V) × (S x).val.Vertex) (d : ℕ) :
    (rawFlatten (restricted G m σ S)).edge v d (.inl w) ↔
      (∃ z, (S v.1).val.graph.edge v.2 d (.inl z) ∧ w = ⟨v.1,z⟩) ∨
      (∃ i, (S v.1).val.graph.edge v.2 d (.inr i) ∧
        G.edge v.1 (σ v.1 i).val (.inl w.1) ∧ (S w.1).val.graph.initial w.2) := by
  constructor
  · rintro (⟨z, hz, he⟩ | ⟨i, hi, h⟩)
    · exact Or.inl ⟨z, hz, Sum.inl.inj he⟩
    · rcases h with ⟨u, ⟨j, hij, hj⟩, hmark, he⟩ | ⟨j, hj, he⟩
      · have hwu : w = u := Sum.inl.inj he
        subst u
        have hji : j = i := Fin.ext hij.symm
        subst j
        exact Or.inr ⟨i, hi, hj, hmark⟩
      · cases he
  · rintro (⟨z, hz, he⟩ | ⟨i, hi, he, hmark⟩)
    · exact Or.inl ⟨z, hz, congrArg Sum.inl he⟩
    · exact Or.inr ⟨i, hi, Or.inl ⟨w, ⟨i,rfl,he⟩, hmark, rfl⟩⟩

private theorem expanded_variable (v : (x : V) × (S x).val.Vertex) (d : ℕ) (j : Fin n) :
    (rawFlatten (expanded G m σ S)).edge v d (.inr j) ↔
      ∃ i, (S v.1).val.graph.edge v.2 d (.inr i) ∧ G.edge v.1 (σ v.1 i).val (.inr j) := by
  change ((∃ z, _ ∧ Sum.inr j = Sum.inl _) ∨ ∃ i,
    (Renaming.renameSystem (σ v.1) (S v.1)).val.graph.edge v.2 d (.inr i) ∧
      ((∃ u, _ ∧ _ ∧ Sum.inr j = Sum.inl u) ∨ ∃ k, G.edge v.1 i.val (.inr k) ∧
        Sum.inr j = Sum.inr k)) ↔ _
  simp only [rename_variable, reduceCtorEq, Sum.inr.injEq, and_false, exists_false,
    false_or]
  constructor
  · rintro ⟨i, ⟨k, hk, rfl⟩, l, hl, rfl⟩
    exact ⟨k, hk, hl⟩
  · rintro ⟨i, hi, he⟩
    exact ⟨σ v.1 i, ⟨i,hi,rfl⟩, j,he,rfl⟩

private theorem restricted_variable (v : (x : V) × (S x).val.Vertex) (d : ℕ) (j : Fin n) :
    (rawFlatten (restricted G m σ S)).edge v d (.inr j) ↔
      ∃ i, (S v.1).val.graph.edge v.2 d (.inr i) ∧ G.edge v.1 (σ v.1 i).val (.inr j) := by
  constructor
  · rintro (⟨z,hz,he⟩ | ⟨i,hi,h⟩)
    · cases he
    · rcases h with ⟨u,hu,hm,he⟩ | ⟨k,⟨l,hil,hl⟩,he⟩
      · cases he
      · have hjk : j = k := Sum.inr.inj he
        subst k
        have hli : l = i := Fin.ext hil.symm
        subst l
        exact ⟨i,hi,hl⟩
  · rintro ⟨i,hi,he⟩
    exact Or.inr ⟨i,hi,Or.inr ⟨j,⟨i,rfl,he⟩,rfl⟩⟩

def raw_iso : PresentationIso (rawFlatten (expanded G m σ S))
    (rawFlatten (restricted G m σ S)) where
  vertex := Equiv.refl _
  label := fun _ => rfl
  initial := fun _ => Iff.rfl
  root := fun _ => Iff.rfl
  edge := by
    intro v d t
    cases t with
    | inl w =>
      exact (restricted_internal G m σ S v w d).trans
        (expanded_internal G m σ S v w d).symm
    | inr j =>
      exact (restricted_variable G m σ S v d j).trans
        (expanded_variable G m σ S v d j).symm

/--
---
conclusion: Lax369799.SupportPorts.restricted_system
---
-/
theorem restricted_system {A B : RankedSet} {n : ℕ} {V : Type} [Fintype V]
    (G : Presentation A n V) (m : V → ℕ)
    (σ : ∀ v, Fin (m v) → Fin (G.label v).1) (S : ∀ v, System B (m v))
    (r : V) (hi : G.initial = {r}) (hr : G.root = ∅)
    (ht : ∀ v d, d < (G.label v).1 → ∃! t, G.edge v d t) :
    ∃ T : System (System B) n, T.val = trim (restricted G m σ S) := by
  refine ⟨⟨trim (restricted G m σ S), ?_⟩, rfl⟩
  apply Lax369799Proofs.Yields.trim_deterministic (restricted G m σ S) r hi hr
  intro v d hd
  let i : Fin (m v) := ⟨d,hd⟩
  obtain ⟨t, hvt, hu⟩ := ht v (σ v i).val (σ v i).isLt
  refine ⟨t, ⟨i,rfl,hvt⟩, ?_⟩
  rintro u ⟨j, hj, he⟩
  have hji : j = i := Fin.ext hj.symm
  subst j
  exact hu u he

/--
---
conclusion: Lax369799.SupportPorts.flatten_iso
---
The identity on pairs of outer and inner vertices preserves internal
edges. Each renamed inner exit is connected through its matching
restricted outer direction, including exits to output variables.
-/
theorem flatten_iso : Nonempty (PresentationIso (flattened (expanded G m σ S))
    (flattened (restricted G m σ S))) := ⟨raw_iso G m σ S⟩

end Lax369799Proofs.SupportPorts
