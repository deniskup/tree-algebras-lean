import Lax369799.PresentationObservations
import Lax369799.FiniteAcceptance

/-!
---
title: Acceptance through resolution values
type: theorem
---
For a language recognized by an unfolding-invariant algebra, universal yield
acceptance is exactly containment of both initial and root observation values
in the accepting set of the algebra.
-/
namespace Lax369799.AcceptanceObservations
open RankedSystems Algebras PresentationObservations

axiom accepting_iff_values {A B : RankedSet} (E : Algebra B) (hE : UnfoldInvariant E)
    (η : RankedMap A B) (F : Set (B 0)) (L : Language A) (hL : Recognizes E η F L)
    {V : Type} [Fintype V] (G : Presentation A 0 V) :
    SyntacticOrder.Accepting L (trim G) ↔
      values E η G ⊆ F ∧ values E η (RootExpansion.startAtRoots G) ⊆ F

end Lax369799.AcceptanceObservations
