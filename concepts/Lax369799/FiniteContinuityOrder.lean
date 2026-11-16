import Lax369799.FiniteYieldContinuity
import Lax369799.FiniteAcceptance

/-!
---
title: Finite yield approximation of contextual acceptance and order
type: theorem
---
Acceptance in a context is determined by all finite sums of yields of
the inserted presentation. Consequently, comparison in the contextual
order is determined by comparison with these finite sums. The yields
are taken over the base alphabet after expansion.
-/
namespace Lax369799.FiniteContinuityOrder
open RankedSystems (RankedSet SetSystem trim)
open FinitePresentations FiniteContexts FiniteContextualOrder FiniteAcceptance

axiom accepting_approximation {A : RankedSet} (L : Algebras.Language A) {k : ℕ}
    (C : Context A k 0) (S : FiniteSystem A k) :
    Accepting L (plug C S) ↔
      ∀ (m : ℕ) (F : Fin m → SetSystem A k),
        (∀ i, Morphisms.Yield (trim S.graph) (F i)) →
        Accepting L (plug C (ofSetSystem (YieldContinuity.finiteSum F)))

axiom order_approximation {A : RankedSet} (L : Algebras.Language A) {n : ℕ}
    (R S : FiniteSystem A n) :
    Below (Accepting L) R S ↔
      ∀ (m : ℕ) (F : Fin m → SetSystem A n),
        (∀ i, Morphisms.Yield (trim S.graph) (F i)) →
        Below (Accepting L) R (ofSetSystem (YieldContinuity.finiteSum F))

end Lax369799.FiniteContinuityOrder
