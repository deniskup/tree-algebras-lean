import Lax369799.FiniteResolutionApproximation
import Lax369799.ObservedSubstitution
import Lax369799.RootExpansion

/-!
---
title: Finite support for root observations
type: theorem
---
A root observation of a substitution uses finitely many initial or root
resolutions of its labels. Retaining these resolutions preserves the
observation. Starting copies distinguish entry through an inner root
from ordinary transitions into an inner initial vertex.
-/
namespace Lax369799.RootResolutionApproximation
open RankedSystems Morphisms FiniteResolutionNormalForms ObservedSubstitution

axiom finite_support {A : RankedSet} {n : ℕ} {V : Type} [Fintype V]
    (P : Presentation (SetSystem A) n V) (R : System A n)
    (hR : InitYield (trim (RootExpansion.startAtRoots
      (FinitePresentations.flattenPresentation (finiteLabels P)))) R) :
    ∃ (m : ℕ) (v : Fin m → V) (c : ∀ i, Component (P.label (v i)).2),
      ∀ (Q : ∀ v, SetSystem A (P.label v).1),
        (∀ i, DirectResolution (if (c i).rooted then uproot (Q (v i)) else Q (v i)) (c i).system) →
        InitYield (trim (RootExpansion.startAtRoots
          (FinitePresentations.flattenPresentation (finiteLabels (replaceLabels P Q))))) R

end Lax369799.RootResolutionApproximation
