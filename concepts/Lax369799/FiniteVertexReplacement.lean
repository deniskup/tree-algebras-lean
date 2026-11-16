import Lax369799.ExpandedSyntacticAlgebra

/-!
---
title: Simultaneous deterministic replacements in finite presentations
type: theorem
---
Marking a vertex gives a context that retains all its incident edges and
boundary marks. Iterating the automaton property over the finite vertex
set replaces every label by a deterministic value below it and preserves
acceptance. No parallel-unary normal form is used.
-/
namespace Lax369799.FiniteVertexReplacement
open RankedSystems (RankedSet)
open FinitePresentations FiniteContexts FiniteContextualOrder FiniteAcceptance
open FiniteSyntacticAlgebra ExpandedSyntacticAlgebra

axiom vertex_context {A B : RankedSet} {n : ℕ} (P : FiniteSystem B n)
    (q : ∀ v : P.Vertex, A (P.graph.label v).1) (v : P.Vertex) :
    ∃ C : Context A (P.graph.label v).1 n,
      ∀ r : ∀ w : P.Vertex, A (P.graph.label w).1,
        (∀ w, w ≠ v → q w = r w) →
        Isomorphic (plug C (atomic (r v))) (withLabels P r)

axiom simultaneous_replacement {A B : RankedSet} (L : Algebras.Language A)
    (hL : Algebras.UnfoldInvariantLanguage L) (hrec : Algebras.Recognizable L)
    (E : SyntacticAlgebra L) (P : FiniteSystem B 0)
    (q : ∀ v : P.Vertex, Carrier (Accepting L) (P.graph.label v).1)
    (hq : AcceptingClass (Accepting L) (E.algebra.eval 0 (withLabels P q))) :
    ∃ r : ∀ v : P.Vertex, Carrier (Accepting L) (P.graph.label v).1,
      (∀ v, FiniteExtremal.Deterministic E.algebra (r v) ∧ ClassBelow (Accepting L) (r v) (q v)) ∧
      AcceptingClass (Accepting L) (E.algebra.eval 0 (withLabels P r))

end Lax369799.FiniteVertexReplacement
