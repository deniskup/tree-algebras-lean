import Lax369799.ExtremalUnaryTypes
import Lax369799.FiniteMarkUnion

/-!
---
title: Splitting outgoing choices in cyclic unary contexts
type: theorem
---
Restrict the outgoing edges of the hole to a set of target vertices.
For a selected unary value, acceptance for a union of targets is
equivalent to acceptance for both restrictions. The context may contain
feedback, roots, and a self-loop at the hole; every vertex is retained.
-/
namespace Lax369799.ContextChoices
open RankedSystems (RankedSet)
open FinitePresentations FiniteContexts FiniteContextualOrder FiniteAcceptance
open FiniteDecomposition FiniteSyntacticAlgebra ExpandedSyntacticAlgebra

noncomputable def restrict {A : RankedSet} {k : ℕ} (C : Context A k 0)
    (p : Set C.system.Vertex) : Context A k 0 where
  system := {
    size := C.system.size
    graph := { C.system.graph with
      edge := fun v d t => C.system.graph.edge v d t ∧
        (v = holeVertex C → match t with | .inl w => p w | .inr _ => False)
      direction_valid := fun v d t h => C.system.graph.direction_valid v d t h.1 } }
  one_hole := C.one_hole

axiom accepting_union {A : RankedSet} (L : Algebras.Language A)
    (E : SyntacticAlgebra L) (b : Carrier (Accepting L) 1)
    (hb : ExtremalUnaryTypes.Selected L E b)
    (C : Context (Carrier (Accepting L)) 1 0) (p q : Set C.system.Vertex) :
    AcceptingClass (Accepting L) (E.algebra.eval 0 (plug (restrict C (p ∪ q)) (atomic b))) ↔
      AcceptingClass (Accepting L) (E.algebra.eval 0 (plug (restrict C p) (atomic b))) ∧
      AcceptingClass (Accepting L) (E.algebra.eval 0 (plug (restrict C q) (atomic b)))

axiom accepting_finite {A : RankedSet} (L : Algebras.Language A)
    (E : SyntacticAlgebra L) (b : Carrier (Accepting L) 1)
    (hb : ExtremalUnaryTypes.Selected L E b)
    (C : Context (Carrier (Accepting L)) 1 0) (s : Finset C.system.Vertex) (hs : s.Nonempty) :
    AcceptingClass (Accepting L) (E.algebra.eval 0 (plug (restrict C (↑s)) (atomic b))) ↔
      ∀ v ∈ s, AcceptingClass (Accepting L)
        (E.algebra.eval 0 (plug (restrict C {v}) (atomic b)))

axiom accepting_all_choices {A : RankedSet} (L : Algebras.Language A)
    (E : SyntacticAlgebra L) (b : Carrier (Accepting L) 1)
    (hb : ExtremalUnaryTypes.Selected L E b)
    (C : Context (Carrier (Accepting L)) 1 0) :
    AcceptingClass (Accepting L) (E.algebra.eval 0 (plug C (atomic b))) ↔
      ∀ v : C.system.Vertex, AcceptingClass (Accepting L)
        (E.algebra.eval 0 (plug (restrict C {v}) (atomic b)))

end Lax369799.ContextChoices
