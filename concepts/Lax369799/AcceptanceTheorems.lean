import Lax369799.SyntacticOrder

/-!
---
title: Acceptance and the syntactic preorder
type: theorem
---
Acceptance is invariant under unfolding. On deterministic systems it
agrees with membership in the original unfold-invariant language. The
syntactic preorder reverses morphisms and preserves acceptance on closed
systems, so acceptance descends to the syntactic quotient.
-/

namespace Lax369799.AcceptanceTheorems
open RankedSystems Morphisms Algebras SyntacticOrder

axiom yield_sum {A : RankedSet} {n : ℕ} (S T U : SetSystem A n) :
    Yield (sum S T) U ↔ Yield S U ∨ Yield T U

axiom accepting_sum {A : RankedSet} (L : Language A) (S T : SetSystem A 0) :
    Accepting L (sum S T) ↔ Accepting L S ∧ Accepting L T

axiom accepting_system {A : RankedSet} (L : Language A)
    (hL : UnfoldInvariantLanguage L) (S : System A 0) :
    Accepting L S.val ↔ S ∈ L

axiom accepting_unfold {A : RankedSet} (L : Language A)
    (S T : SetSystem A 0) (h : UnfoldEquivalent S T) :
    Accepting L S ↔ Accepting L T

axiom syntactic_morphism {A : RankedSet} (L : Language A) {n : ℕ}
    {S T : SetSystem A n} (f : Morphism S T) : SyntacticBelow L T S

axiom syntactic_acceptance {A : RankedSet} (L : Language A)
    {S T : SetSystem A 0} (h : SyntacticBelow L S T) :
    Accepting L S → Accepting L T

end Lax369799.AcceptanceTheorems
