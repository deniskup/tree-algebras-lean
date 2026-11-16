import Lax369799.ContextChoices

/-!
---
title: Functional restrictions of selected unary graphs
type: theorem
---
In a finite unary/nullary presentation, selected unary labels allow each
outgoing target set to be split independently. Acceptance is equivalent
to acceptance of all functional restrictions, including in the presence
of cycles. Restrictions retain all vertices and all initial/root marks.
-/
namespace Lax369799.GraphChoices
open RankedSystems (RankedSet)
open FinitePresentations FiniteContexts FiniteContextualOrder FiniteAcceptance
open FiniteSyntacticAlgebra ExpandedSyntacticAlgebra

noncomputable def restrictRow {A : RankedSet} (P : FiniteSystem A 0)
    (v : P.Vertex) (p : Set P.Vertex) : FiniteSystem A 0 where
  size := P.size
  graph := { P.graph with
    edge := fun w d t => P.graph.edge w d t ∧
      (w = v → match t with | .inl u => p u | .inr _ => False)
    direction_valid := fun w d t h => P.graph.direction_valid w d t h.1 }


noncomputable def chooseRows {A : RankedSet} (P : FiniteSystem A 0)
    (s : Finset P.Vertex) (f : P.Vertex → P.Vertex) : FiniteSystem A 0 where
  size := P.size
  graph := { P.graph with
    edge := fun v d t => P.graph.edge v d t ∧ (v ∈ s → t = .inl (f v))
    direction_valid := fun v d t h => P.graph.direction_valid v d t h.1 }


axiom row_choices {A : RankedSet} (L : Algebras.Language A)
    (E : SyntacticAlgebra L) (P : FiniteSystem (Carrier (Accepting L)) 0)
    (v : P.Vertex) (hv : (P.graph.label v).1 = 1)
    (hs : ExtremalUnaryTypes.Selected L E (hv ▸ (P.graph.label v).2)) :
    AcceptingClass (Accepting L) (E.algebra.eval 0 P) ↔
      ∀ w : P.Vertex, AcceptingClass (Accepting L)
        (E.algebra.eval 0 (restrictRow P v {w}))

axiom finite_choices {A : RankedSet} (L : Algebras.Language A)
    (E : SyntacticAlgebra L) (P : FiniteSystem (Carrier (Accepting L)) 0)
    (hu : ∀ v, (P.graph.label v).1 ≤ 1)
    (hs : ∀ v (h : (P.graph.label v).1 = 1),
      ExtremalUnaryTypes.Selected L E (h ▸ (P.graph.label v).2))
    (s : Finset P.Vertex) :
    AcceptingClass (Accepting L) (E.algebra.eval 0 P) ↔
      ∀ f : P.Vertex → P.Vertex, AcceptingClass (Accepting L) (E.algebra.eval 0 (chooseRows P s f))

axiom chosen_functional {A : RankedSet} (P : FiniteSystem A 0)
    (f : P.Vertex → P.Vertex) (v : P.Vertex) (d : ℕ) (t u : P.Vertex ⊕ Fin 0)
    (ht : (chooseRows P Finset.univ f).graph.edge v d t)
    (hu : (chooseRows P Finset.univ f).graph.edge v d u) : t = u

def Admissible {A : RankedSet} (P : FiniteSystem A 0) (f : P.Vertex → P.Vertex) : Prop :=
  ∀ v, (∃ d w, P.graph.edge v d (.inl w)) → ∃ d, P.graph.edge v d (.inl (f v))


axiom admissible_test {A : RankedSet} (L : Algebras.Language A)
    (E : SyntacticAlgebra L) (P : FiniteSystem (Carrier (Accepting L)) 0)
    (hu : ∀ v, (P.graph.label v).1 ≤ 1)
    (hs : ∀ v (h : (P.graph.label v).1 = 1),
      ExtremalUnaryTypes.Selected L E (h ▸ (P.graph.label v).2)) :
    AcceptingClass (Accepting L) (E.algebra.eval 0 P) ↔
      ∀ f : P.Vertex → P.Vertex, Admissible P f →
        AcceptingClass (Accepting L) (E.algebra.eval 0 (chooseRows P Finset.univ f))

end Lax369799.GraphChoices
