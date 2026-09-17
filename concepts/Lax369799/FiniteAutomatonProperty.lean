import Lax369799.FiniteExtremal

/-!
---
title: Automaton property of the unpruned syntactic algebra
type: theorem
---
If the unary contextual sort is finite, every value in an accepting
context can be replaced by a deterministic value below it while preserving
acceptance. The proof uses the unpruned normal form and its boundary data,
without a yield-continuity axiom.
-/
namespace Lax369799.FiniteAutomatonProperty
open RankedSystems (RankedSet)
open FinitePresentations FiniteContexts FiniteContextualOrder FiniteSyntacticAlgebra
open FiniteAcceptance FiniteExtremal

axiom automaton_property {A : RankedSet} (L : Algebras.Language A)
    (E : Algebra (Carrier (Accepting L)))
    (hE : ∀ n (S : FiniteSystem (FiniteSystem A) n),
      E.eval n (relabel (quotientMap (Accepting L)) S) = quotientMap (Accepting L) n (flatten S))
    (hfinite : Finite (Carrier (Accepting L) 1))
    {k : ℕ} (C : Context (Carrier (Accepting L)) k 0) (a : Carrier (Accepting L) k)
    (ha : AcceptingClass (Accepting L) (E.eval 0 (plug C (atomic a)))) :
    ∃ δ, Deterministic E δ ∧ ClassBelow (Accepting L) δ a ∧
      AcceptingClass (Accepting L) (E.eval 0 (plug C (atomic δ)))

end Lax369799.FiniteAutomatonProperty
