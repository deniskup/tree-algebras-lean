import Lax369799.FiniteResolutionApproximation

/-!
---
title: Finite resolution approximation in a context
type: theorem
---
A direct resolution in a context needs only a finite family of direct
resolutions at its hole. Keeping their sum inside the context permits
independent choices at different occurrences. This is the approximation
behind Corollary 46 of arXiv v6 (Corollary 50 in the revised manuscript),
and its consequence for initial yields, using the earlier reachable interface.
-/
namespace Lax369799.ContextResolutionApproximation
open RankedSystems Morphisms Flattening FiniteResolutionNormalForms

axiom direct_approximation {A : RankedSet} {k n : ℕ}
    (C : SetContext A k n) (S : SetSystem A k) (R : System A n)
    (hR : DirectResolution (plug C S) R) :
    ∃ (m : ℕ) (c : Fin m → Component S) (U : System A n),
      (∀ i, (c i).rooted = false) ∧
      DirectResolution (plug C (trim (family c).graph)) U ∧ UnfoldsTo R.val U.val

axiom initial_yields {A : RankedSet} {k n : ℕ}
    (C : SetContext A k n) (S : SetSystem A k) (R : System A n) :
    InitYield (plug C S) R ↔
      ∃ (m : ℕ) (c : Fin m → Component S),
        (∀ i, (c i).rooted = false) ∧ InitYield (plug C (trim (family c).graph)) R

axiom root_yields {A : RankedSet} {k n : ℕ}
    (C : SetContext A k n) (S : SetSystem A k) (R : System A n) :
    InitYield (uproot (plug C S)) R ↔
      ∃ (m : ℕ) (c : Fin m → Component S),
        InitYield (uproot (plug C (trim (family c).graph))) R

axiom yields {A : RankedSet} {k n : ℕ}
    (C : SetContext A k n) (S : SetSystem A k) (R : SetSystem A n) :
    Yield (plug C S) R ↔
      ∃ (m : ℕ) (c : Fin m → Component S),
        Yield (plug C (trim (family c).graph)) R

end Lax369799.ContextResolutionApproximation
