import Lax369799.ProfileSubstitution

/-!
---
title: Substitution and yield inclusion
type: theorem
---
Local yield inclusion transfers resolutions of a flattening. Variable
splitting allows different occurrences of an inner variable to take
different outer successors.
-/
namespace Lax369799.YieldSubstitution
open RankedSystems Morphisms Flattening ProfileSubstitution

axiom transfer_resolution {A : RankedSet} {n : ℕ}
    (P : SetSystem (SetSystem A) n) (Q : ∀ v, SetSystem A (P.graph.label v).1)
    (hQ : ∀ v, YieldBelow (Inner P v) (Q v))
    (R : System A n) (hR : DirectResolution (flatten P) R) :
    ∃ U : System A n, DirectResolution (flatten (withLabels P Q)) U ∧
      UnfoldsTo R.val U.val

axiom flatten_mono {A : RankedSet} {n : ℕ}
    (P : SetSystem (SetSystem A) n) (Q : ∀ v, SetSystem A (P.graph.label v).1)
    (hQ : ∀ v, YieldBelow (Inner P v) (Q v)) :
    YieldBelow (flatten P) (flatten (withLabels P Q))

end Lax369799.YieldSubstitution
