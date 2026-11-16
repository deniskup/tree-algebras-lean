import Lax369799.SelectedChoicePreservation
import Lax369799.ParallelReplacement

/-!
---
title: Parallel transitions with selected unary components
type: theorem
---
Refine the components of an accepting parallel tuple one at a time.
Rank-one extremal replacement preserves acceptance and decreases each
component. Consequently the parallel transition inequality is retained,
and every resulting component preserves binary choices of closed
continuations.
-/
namespace Lax369799.SelectedParallel
open RankedSystems (RankedSet)
open FinitePresentations FiniteContexts FiniteContextualOrder FiniteAcceptance
open FiniteSyntacticAlgebra ExpandedSyntacticAlgebra

axiom accepting_parallel {A : RankedSet} (L : Algebras.Language A)
    (hL : Algebras.UnfoldInvariantLanguage L) (hrec : Algebras.Recognizable L)
    (E : SyntacticAlgebra L) {k : ℕ} (hk : 1 ≤ k)
    (C : Context (Carrier (Accepting L)) k 0) (a : Carrier (Accepting L) k)
    (ha : AcceptingClass (Accepting L) (E.algebra.eval 0 (plug C (atomic a)))) :
    ∃ b : Fin k → Carrier (Accepting L) 1,
      (∀ i, ExtremalUnaryTypes.Selected L E (b i)) ∧
      ClassBelow (Accepting L) (E.algebra.eval k (ofSetSystem (DeterministicElements.parallel b))) a ∧
      AcceptingClass (Accepting L) (E.algebra.eval 0 (plug C
        (atomic (E.algebra.eval k (ofSetSystem (DeterministicElements.parallel b))))))

end Lax369799.SelectedParallel
