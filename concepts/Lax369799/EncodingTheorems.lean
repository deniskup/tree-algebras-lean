import Lax369799.TransitionEncoding

/-!
---
title: Correctness of ranked transition encodings
type: theorem
---
Every finite reachable transition system has a ranked encoding. Ranked
bisimilarity coincides with usual bisimilarity of decodings, as asserted
by `lemma:bisimulation-is-bisimulation` in Section 6.1.
-/

namespace Lax369799.EncodingTheorems
open RankedSystems TransitionSystems TransitionEncoding

axiom encoding_exists {P : Type} (S : TransitionSystem P) :
  ∃ T : System (TransitionAlphabet P) 0, decode T = S

axiom bisimulation_iff {P : Type} (S T : System (TransitionAlphabet P) 0) :
  RankedBisimilar S T ↔ Bisimilar (decode S) (decode T)

end Lax369799.EncodingTheorems
