import Lax369799.DirectionReindexing
import Lax369799.SetSystemAlgebras

/-!
---
title: Substitution after reindexing directions
type: theorem
---
Reindexing the directions of an outer system and renaming the ports of
its substituted pieces give the same flattened graph. Evaluation is
therefore unchanged. All vertices and marks are retained.
-/
namespace Lax369799.PortReindexing
open RankedSystems (RankedSet System)
open TransitionEncoding FinitePresentations SetSystemAlgebras DirectionReindexing

def rename {Y : RankedSet} {m n : ℕ} (P : FiniteSystem Y m) (σ : Fin m → Fin n) :
    FiniteSystem Y n where
  size := P.size
  graph := {
    label := P.graph.label
    initial := P.graph.initial
    root := P.graph.root
    edge := fun v d t => match t with
      | .inl w => P.graph.edge v d (.inl w)
      | .inr i => ∃ j, σ j = i ∧ P.graph.edge v d (.inr j)
    direction_valid := by
      intro v d t h
      cases t with
      | inl w => exact P.graph.direction_valid _ _ _ h
      | inr i => obtain ⟨j, _, hj⟩ := h; exact P.graph.direction_valid _ _ _ hj }


axiom evaluation {P : Type} {Y : RankedSet} (S : System (TransitionAlphabet P) 0)
    (R : Reindexing S) (B : ∀ v : S.val.Vertex, FiniteSystem Y (R.arity v)) (E : SetAlgebra Y) :
    E.eval 0 (withLabels (ofSetSystem S.val) (fun v => E.eval _ (rename (B v) (R.map v)))) =
      E.eval 0 (withLabels (ofSetSystem (DirectionReindexing.system S R).val)
        (fun v => E.eval _ (B v)))

end Lax369799.PortReindexing
