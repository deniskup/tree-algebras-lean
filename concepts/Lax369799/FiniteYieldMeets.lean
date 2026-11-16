import Lax369799.FiniteContinuityOrder

/-!
---
title: Finite sums are contextual meets
type: theorem
---
A finite disjoint sum represents the meet of its summands in the
contextual order. The empty sum represents the greatest element.
Together with finite yield approximation, this gives continuity over
base-alphabet yields.
-/
namespace Lax369799.FiniteYieldMeets
open RankedSystems (RankedSet SetSystem trim)
open FinitePresentations FiniteContextualOrder FiniteAcceptance

axiom finite_meet {A : RankedSet} (L : Algebras.Language A) {n m : ℕ}
    (R : FiniteSystem A n) (F : Fin m → SetSystem A n) :
    Below (Accepting L) R (ofSetSystem (YieldContinuity.finiteSum F)) ↔
      ∀ i, Below (Accepting L) R (ofSetSystem (F i))

axiom yield_lower_bound {A : RankedSet} (L : Algebras.Language A) {n : ℕ}
    (R S : FiniteSystem A n) :
    Below (Accepting L) R S ↔
      ∀ T : SetSystem A n, Morphisms.Yield (trim S.graph) T →
        Below (Accepting L) R (ofSetSystem T)

end Lax369799.FiniteYieldMeets
