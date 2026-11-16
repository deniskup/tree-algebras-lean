import Lax369799.YieldContinuity
import Lax369799.FiniteContexts
import Lax369799.InitialResolutionApproximation

/-!
---
title: Yield continuity for finite-presentation contexts
type: theorem
---
The finite approximation of yields also holds for contexts retaining
unreachable vertices. Substitution precedes the final reachable
restriction, so roots supplied at an unreachable hole remain observable.
-/
namespace Lax369799.FiniteYieldContinuity
open RankedSystems Morphisms

noncomputable def insert {A : RankedSet} {k n : ℕ}
    (C : FiniteContexts.Context A k n) (S : SetSystem A k) : SetSystem A n :=
  trim (FiniteContexts.plug C (FinitePresentations.ofSetSystem S)).graph

axiom context_mono {A : RankedSet} {k n : ℕ}
    (C : FiniteContexts.Context A k n) (S T : SetSystem A k) (h : YieldBelow S T) :
    YieldBelow (insert C S) (insert C T)

axiom continuity {A : RankedSet} {k n : ℕ}
    (C : FiniteContexts.Context A k n) (S : SetSystem A k) (R : SetSystem A n) :
    Yield (insert C S) R ↔
      ∃ (m : ℕ) (F : Fin m → SetSystem A k),
        (∀ i, Yield S (F i)) ∧ Yield (insert C (YieldContinuity.finiteSum F)) R

end Lax369799.FiniteYieldContinuity
