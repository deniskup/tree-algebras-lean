import Lax369799Proofs.Pullbacks

namespace Lax369799Proofs.MorphismTheorems
open Lax369799.RankedSystems Lax369799.Morphisms

/--
---
conclusion: Lax369799.MorphismTheorems.unfold_equivalence
---
Reflexivity uses the identity cover and symmetry exchanges projections.
For transitivity, pull back the two covers of the middle system.
-/
theorem unfold_equivalence (A : RankedSet) (n : ℕ) :
    Equivalence (@UnfoldEquivalent A n) := by
  refine ⟨?_, ?_, ?_⟩
  · intro S
    exact ⟨S, ⟨identity S, identity_surjective S⟩, ⟨identity S, identity_surjective S⟩⟩
  · rintro S T ⟨U, hS, hT⟩
    exact ⟨U, hT, hS⟩
  · rintro S T U ⟨P, ⟨pS, hpS⟩, ⟨pT, hpT⟩⟩ ⟨Q, ⟨qT, hqT⟩, ⟨qU, hqU⟩⟩
    obtain ⟨R, rP, rQ, _, _, hQ, hP⟩ := Lax369799Proofs.Pullbacks.pullback pT qT
    obtain ⟨s, _, hs⟩ := composition rP pS
    obtain ⟨u, _, hu⟩ := composition rQ qU
    exact ⟨R, ⟨s, hs (hP hqT) hpS⟩, ⟨u, hu (hQ hpT) hqU⟩⟩


end Lax369799Proofs.MorphismTheorems
