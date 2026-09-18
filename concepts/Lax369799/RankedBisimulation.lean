import Lax369799.TransitionEncoding

/-!
---
title: Bisimulation under ranked decoding
type: theorem
---
Ordinary bisimilarity is an equivalence relation. Ranked unfolding and
isomorphism of decodings both preserve it, so the equivalence generated
by these operations implies ordinary bisimilarity after decoding.
-/
namespace Lax369799.RankedBisimulation
open RankedSystems TransitionSystems TransitionEncoding

axiom bisimilarity_equivalence (P : Type) : Equivalence (@Bisimilar P)

axiom ranked_forward {P : Type} (S T : System (TransitionAlphabet P) 0)
    (h : RankedBisimilar S T) : Bisimilar (decode S) (decode T)

end Lax369799.RankedBisimulation
