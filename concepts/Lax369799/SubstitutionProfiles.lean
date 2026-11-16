import Lax369799.SupportEvaluation
import Lax369799.PolynomialContexts

/-!
---
title: Substitution congruence for compacted evaluations
type: theorem
---
Pointwise equality of the supported-evaluation profiles of inner systems
is preserved by deterministic substitution. A common compacted outer
shape compares their supported evaluations after the unused ports are
removed.
-/

namespace Lax369799.SubstitutionProfiles
open RankedSystems SupportedAlgebras
open SupportEvaluation (Equivalent)

axiom pointwise_congruence {A B : RankedSet} (E : Algebra B) {n : ℕ}
    (P : System A n) (q s : ∀ v, System B (P.val.graph.label v).1)
    (hqs : ∀ v, Equivalent E (q v) (s v))
    (F H : System B n)
    (hF : Lax369799.Flattening.SystemFlattening (PolynomialContexts.withLabels P q) F)
    (hH : Lax369799.Flattening.SystemFlattening (PolynomialContexts.withLabels P s) H) :
    Equivalent E F H

end Lax369799.SubstitutionProfiles
