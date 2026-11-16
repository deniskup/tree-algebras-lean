import Lax369799.PortReindexing
import Lax369799Proofs.DirectionReindexing
import Lax369799Proofs.SetSystemAlgebras
import Lax369799Proofs.FiniteAlgebraMeets
import Lax369799Proofs.UntrimmedFlattening

namespace Lax369799Proofs.PortReindexing
set_option backward.isDefEq.respectTransparency false
open Lax369799
open RankedSystems (RankedSet System Presentation)
open TransitionEncoding FinitePresentations SetSystemAlgebras
open Lax369799.DirectionReindexing

open Lax369799.PortReindexing

variable {P : Type} {Y : RankedSet} (S : System (TransitionAlphabet P) 0) (R : Reindexing S)
    (B : ∀ v : S.val.Vertex, FiniteSystem Y (R.arity v))

private abbrev G := (withLabels (ofSetSystem S.val) (fun v => rename (B v) (R.map v))).graph
private abbrev H := (withLabels (ofSetSystem (DirectionReindexing.system S R).val) B).graph

private theorem edge_G (v w : (x : S.val.Vertex) × (B x).Vertex) (d : ℕ) :
    (flattenPresentation (G S R B)).edge v d (.inl w) ↔
      (∃ z, (B v.1).graph.edge v.2 d (.inl z) ∧ w = ⟨v.1, z⟩) ∨
      (∃ i, (B v.1).graph.edge v.2 d (.inr i) ∧
        S.val.graph.edge v.1 (R.map v.1 i).val (.inl w.1) ∧ (B w.1).graph.initial w.2) := by
  constructor
  · rintro (⟨z, hz, he⟩ | ⟨i, ⟨j, hj, he⟩, (⟨u, hu, hi, heq⟩ | ⟨j, hj, heq⟩)⟩)
    · exact Or.inl ⟨z, hz, Sum.inl.inj he⟩
    · have hwu : w = u := Sum.inl.inj heq
      subst u
      subst i
      exact Or.inr ⟨j, he, hu, hi⟩
    · cases heq
  · rintro (⟨z, hz, he⟩ | ⟨i, hi, he, hmark⟩)
    · exact Or.inl ⟨z, hz, congrArg Sum.inl he⟩
    · exact Or.inr ⟨R.map v.1 i, ⟨i, rfl, hi⟩, Or.inl ⟨w, he, hmark, rfl⟩⟩

private theorem edge_H (v w : (x : S.val.Vertex) × (B x).Vertex) (d : ℕ) :
    (flattenPresentation (H S R B)).edge v d (.inl w) ↔
      (∃ z, (B v.1).graph.edge v.2 d (.inl z) ∧ w = ⟨v.1, z⟩) ∨
      (∃ i, (B v.1).graph.edge v.2 d (.inr i) ∧
        S.val.graph.edge v.1 (R.map v.1 i).val (.inl w.1) ∧ (B w.1).graph.initial w.2) := by
  constructor
  · rintro (⟨z, hz, he⟩ | ⟨i, he, (⟨u, ⟨j, hj, hu⟩, hi, heq⟩ | ⟨j, hj, heq⟩)⟩)
    · exact Or.inl ⟨z, hz, Sum.inl.inj he⟩
    · have hwu : w = u := Sum.inl.inj heq
      subst u
      have hji : j = i := Fin.ext hj.symm
      subst j
      exact Or.inr ⟨i, he, hu, hi⟩
    · cases heq
  · rintro (⟨z, hz, he⟩ | ⟨i, hi, he, hmark⟩)
    · exact Or.inl ⟨z, hz, congrArg Sum.inl he⟩
    · exact Or.inr ⟨i, hi, Or.inl ⟨w, ⟨i, rfl, he⟩, hmark, rfl⟩⟩

def rawIso : PresentationIso (flattenPresentation (G S R B)) (flattenPresentation (H S R B)) where
  vertex := Equiv.refl _
  label := fun _ => rfl
  initial := fun _ => Iff.rfl
  root := by
    intro v
    change ((B v.1).graph.root v.2 ∨ (False ∧ (B v.1).graph.initial v.2)) ↔
      ((B v.1).graph.root v.2 ∨ (S.val.graph.root v.1 ∧ (B v.1).graph.initial v.2))
    rw [S.property.2.1]
    exact Iff.rfl
  edge := by
    intro v d t
    cases t with
    | inl w => exact (edge_H S R B v w d).trans (edge_G S R B v w d).symm
    | inr i => exact Fin.elim0 i

/--
---
conclusion: Lax369799.PortReindexing.evaluation
---
Use the identity on flattened vertices. A port renamed to an old
direction connects exactly to that direction's reindexed successors.
Associativity identifies evaluation of the two flattened presentations.
-/
theorem evaluation (E : SetAlgebra Y) :
    E.eval 0 (withLabels (ofSetSystem S.val) (fun v => E.eval _ (rename (B v) (R.map v)))) =
      E.eval 0 (withLabels (ofSetSystem (DirectionReindexing.system S R).val)
        (fun v => E.eval _ (B v))) := by
  have hi : Isomorphic (enumerate (flattenPresentation (G S R B)))
      (enumerate (flattenPresentation (H S R B))) := ⟨UntrimmedFlattening.isoTrans
        (UntrimmedFlattening.isoSymm (UntrimmedFlattening.reindexIso _ (Fintype.equivFin _)))
        (UntrimmedFlattening.isoTrans (rawIso S R B)
          (UntrimmedFlattening.reindexIso _ (Fintype.equivFin _)))⟩
  have h := E.isomorphic 0 _ _ hi
  change E.eval 0 (flatten (withLabels (ofSetSystem S.val) (fun v => rename (B v) (R.map v)))) =
    E.eval 0 (flatten (withLabels (ofSetSystem (DirectionReindexing.system S R).val) B)) at h
  rw [← E.associative, ← E.associative] at h
  exact h

end Lax369799Proofs.PortReindexing
