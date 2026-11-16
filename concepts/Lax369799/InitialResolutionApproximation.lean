import Lax369799.RootResolutionApproximation

/-!
---
title: Finite support for initial observations
type: theorem
---
Initial observations of a substitution depend on finitely many initial
resolutions of its labels, including when the outer presentation retains
unreachable vertices. Removing root marks before factoring preserves
these observations.
-/
namespace Lax369799.InitialResolutionApproximation
open RankedSystems Morphisms FiniteResolutionNormalForms ObservedSubstitution

axiom finite_support {A : RankedSet} {n : ℕ} {V : Type} [Fintype V]
    (P : Presentation (SetSystem A) n V) (R : System A n)
    (hR : InitYield (trim (FinitePresentations.flattenPresentation (finiteLabels P))) R) :
    ∃ (m : ℕ) (v : Fin m → V) (c : ∀ i, Component (P.label (v i)).2),
      (∀ i, (c i).rooted = false) ∧
      ∀ (Q : ∀ v, SetSystem A (P.label v).1),
        (∀ i, DirectResolution (Q (v i)) (c i).system) →
        InitYield (trim (FinitePresentations.flattenPresentation
          (finiteLabels (replaceLabels P Q)))) R

end Lax369799.InitialResolutionApproximation
