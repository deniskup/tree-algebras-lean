import Lax369799.FiniteVertexReplacement

/-!
---
title: Finite iteration of context-preserving local choices
type: theorem
---
Any rule that replaces a label in its current accepting context can be
iterated over all vertices of a finite presentation. The local relation
records both the original and the chosen label.
-/
namespace Lax369799.FiniteLocalReplacement
open RankedSystems (RankedSet)
open FinitePresentations FiniteContexts FiniteSyntacticAlgebra

axiom simultaneous {A B : RankedSet} (E : Algebra A) (F : Set (A 0))
    (G : ∀ n, A n → A n → Prop)
    (hG : ∀ k (C : Context A k 0) (a : A k), E.eval 0 (plug C (atomic a)) ∈ F →
      ∃ b, G k a b ∧ E.eval 0 (plug C (atomic b)) ∈ F)
    (P : FiniteSystem B 0) (q : ∀ v : P.Vertex, A (P.graph.label v).1)
    (hq : E.eval 0 (withLabels P q) ∈ F) :
    ∃ r : ∀ v : P.Vertex, A (P.graph.label v).1,
      (∀ v, G _ (q v) (r v)) ∧ E.eval 0 (withLabels P r) ∈ F

end Lax369799.FiniteLocalReplacement
