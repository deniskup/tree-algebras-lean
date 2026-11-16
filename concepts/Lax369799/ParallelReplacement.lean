import Lax369799.SplitExtremal
import Lax369799.ExpandedSyntacticAlgebra

/-!
---
title: Parallel replacements in accepting contexts
type: theorem
---
The split extremal witness is a parallel tuple of unary values. It lies
below the original value and preserves acceptance in the chosen context.
This is an existence result for accepting contexts, not a normal form for
all deterministic values.
-/
namespace Lax369799.ParallelReplacement
open RankedSystems (RankedSet)
open FinitePresentations FiniteContexts FiniteContextualOrder FiniteAcceptance FiniteSyntacticAlgebra
open ExpandedSyntacticAlgebra

axiom accepting_parallel {A : RankedSet} (L : Algebras.Language A)
    (hL : Algebras.UnfoldInvariantLanguage L) (hrec : Algebras.Recognizable L)
    (E : SyntacticAlgebra L) {k : ℕ} (hk : 1 ≤ k)
    (C : Context (Carrier (Accepting L)) k 0) (a : Carrier (Accepting L) k)
    (ha : AcceptingClass (Accepting L) (E.algebra.eval 0 (plug C (atomic a)))) :
    ∃ b : Fin k → Carrier (Accepting L) 1,
      ClassBelow (Accepting L) (E.algebra.eval k (ofSetSystem (DeterministicElements.parallel b))) a ∧
      AcceptingClass (Accepting L) (E.algebra.eval 0 (plug C
        (atomic (E.algebra.eval k (ofSetSystem (DeterministicElements.parallel b))))))

end Lax369799.ParallelReplacement
