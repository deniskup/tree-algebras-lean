import Lax369799.SupportedRecognition
import Lax369799Proofs.SupportedCompletion
import Lax369799Proofs.RecognitionClosure
import Lax369799Proofs.RecognitionProjection
import Lax369799Proofs.BoundedProfileRefinement

set_option backward.isDefEq.respectTransparency false
namespace Lax369799Proofs.SupportedRecognition
open Lax369799
open RankedSystems Algebras

/--
---
conclusion: Lax369799.SupportedRecognition.language_invariant
---
Relabel a common unfolding by the recognizing letter map. Equal
supported evaluations give equal membership in the accepting subset.
-/
theorem language_invariant {A B : RankedSet} (E : SupportedAlgebras.Algebra B)
    (hE : SupportedAlgebras.UnfoldInvariant E) (η : RankedMap A B) (F : Set (B 0))
    (L : Language A) (hL : SupportedAlgebras.Recognizes E η F L) : UnfoldInvariantLanguage L := by
  intro S T h
  let S' := (SupportedSystems.closedEquiv A).symm S
  let T' := (SupportedSystems.closedEquiv A).symm T
  have he := hE 0 (SupportedSystems.relabel η S') (SupportedSystems.relabel η T')
    (SystemSubstitution.relabel_unfold η h)
  exact (hL S').trans ((Iff.of_eq (congrArg (fun b => b ∈ F) he)).trans (hL T').symm)

/--
---
conclusion: Lax369799.SupportedRecognition.complement
---
Complete the recognizer, complement its accepting set, and restrict back.
-/
theorem complement {A : RankedSet} (L : Language A) (h : SupportedAlgebras.Recognizable L) :
    SupportedAlgebras.Recognizable Lᶜ :=
  SupportedAlgebras.legacy_recognizable _ (RecognitionClosure.complement L
    (SupportedCompletion.legacy_recognizable L h))

/--
---
conclusion: Lax369799.SupportedRecognition.intersection
---
Products of the completed recognizers preserve finite sorts.
-/
theorem intersection {A : RankedSet} (L K : Language A)
    (hL : SupportedAlgebras.Recognizable L) (hK : SupportedAlgebras.Recognizable K) :
    SupportedAlgebras.Recognizable (L ∩ K) :=
  SupportedAlgebras.legacy_recognizable _ (RecognitionClosure.intersection L K
    (SupportedCompletion.legacy_recognizable L hL) (SupportedCompletion.legacy_recognizable K hK))

/--
---
conclusion: Lax369799.SupportedRecognition.union
---
Use the product recognizer with disjunctive acceptance.
-/
theorem union {A : RankedSet} (L K : Language A)
    (hL : SupportedAlgebras.Recognizable L) (hK : SupportedAlgebras.Recognizable K) :
    SupportedAlgebras.Recognizable (L ∪ K) :=
  SupportedAlgebras.legacy_recognizable _ (RecognitionClosure.union L K
    (SupportedCompletion.legacy_recognizable L hL) (SupportedCompletion.legacy_recognizable K hK))

/--
---
conclusion: Lax369799.SupportedRecognition.inverse_relabel
---
Compose the alphabet map with the map of the completed recognizer.
-/
theorem inverse_relabel {A B : RankedSet} (η : RankedMap A B) (L : Language B)
    (hL : SupportedAlgebras.Recognizable L) :
    SupportedAlgebras.Recognizable {S | relabelSystem η S ∈ L} :=
  SupportedAlgebras.legacy_recognizable _ (RecognitionClosure.inverse_relabel η L
    (SupportedCompletion.legacy_recognizable L hL))

/--
---
conclusion: Lax369799.SupportedRecognition.projection
---
Apply finite powerset recognition after completion, then restrict to the
supported domain.
-/
theorem projection {A B : RankedSet} (η : RankedMap A B)
    (hη : ∀ n, Function.Surjective (η n)) (L : Language A)
    (hL : SupportedAlgebras.Recognizable L) :
    SupportedAlgebras.Recognizable (RecognitionProjection.Projected η L) :=
  SupportedAlgebras.legacy_recognizable _ (RecognitionProjection.recognizable η hη L
    (SupportedCompletion.legacy_recognizable L hL))

/--
---
conclusion: Lax369799.SupportedRecognition.syntactic_rankwise_finite
---
Complete the finite supported recognizer and apply the proved bounded
profile refinement for the unpruned contextual quotient.
-/
theorem syntactic_rankwise_finite {A : RankedSet} (L : Language A)
    (hL : UnfoldInvariantLanguage L) (hrec : SupportedAlgebras.Recognizable L) :
    RankwiseFinite (FiniteContextualOrder.Carrier (FiniteAcceptance.Accepting L)) :=
  BoundedProfileRefinement.finite_carrier_recognizable L hL
    (SupportedCompletion.legacy_recognizable L hrec)

end Lax369799Proofs.SupportedRecognition
