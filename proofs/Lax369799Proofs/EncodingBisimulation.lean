import Lax369799.EncodingTheorems
import Lax369799Proofs.RankedBisimulation
import Lax369799Proofs.RankedLifting
import Lax369799Proofs.CommonBisimulationQuotient

namespace Lax369799Proofs.EncodingBisimulation
open Lax369799.RankedSystems Lax369799.Morphisms
open Lax369799.TransitionSystems Lax369799.TransitionEncoding

private theorem same_decoding {P : Type} (S T : System (TransitionAlphabet P) 0)
    (h : decode S = decode T) : RankedBisimilar S T := by
  apply Relation.EqvGen.rel
  apply Or.inr
  rw [h]
  exact ⟨Equiv.refl _, rfl, fun _ => rfl, fun _ _ => Iff.rfl⟩

private theorem morphism_ranked {P : Type} (S T : System (TransitionAlphabet P) 0)
    (f : Morphism S.val T.val) : RankedBisimilar S T := by
  apply Relation.EqvGen.rel
  exact Or.inl ⟨S.val,
    ⟨MorphismTheorems.identity _, MorphismTheorems.identity_surjective _⟩,
    ⟨f, MorphismTheorems.system_morphism_locally_surjective S T f⟩⟩

/--
---
conclusion: Lax369799.EncodingTheorems.bisimulation_iff
---
The forward implication follows by decoding ranked generators. For the
converse, map both decoded systems to a common bisimulation quotient and
rank each functional map. Re-encodings of the same transition system are
generators, while the two ranked maps supply common unfoldings.
-/
theorem bisimulation_iff {P : Type} (S T : System (TransitionAlphabet P) 0) :
    RankedBisimilar S T ↔ Bisimilar (decode S) (decode T) := by
  refine ⟨RankedBisimulation.ranked_forward S T, ?_⟩
  intro h
  obtain ⟨Q, ⟨f⟩, ⟨g⟩⟩ := BisimulationQuotient.common_quotient (decode S) (decode T) h
  obtain ⟨S', U, hS, hU, ⟨sf⟩⟩ := RankedLifting.map_lift (decode S) Q f
  obtain ⟨T', V, hT, hV, ⟨tg⟩⟩ := RankedLifting.map_lift (decode T) Q g
  have h₁ := same_decoding S S' hS.symm
  have h₂ := morphism_ranked S' U sf
  have h₃ := same_decoding U V (hU.trans hV.symm)
  have h₄ := Relation.EqvGen.symm _ _ (morphism_ranked T' V tg)
  have h₅ := same_decoding T' T hT
  exact Relation.EqvGen.trans _ _ _ h₁ (Relation.EqvGen.trans _ _ _ h₂
    (Relation.EqvGen.trans _ _ _ h₃ (Relation.EqvGen.trans _ _ _ h₄ h₅)))

end Lax369799Proofs.EncodingBisimulation
