import Lax369799.SupportedAlgebras
import Lax369799.RecognitionClosure
import Lax369799.RecognitionProjection
import Lax369799.BoundedProfileRefinement

/-!
---
title: Language invariance, closure, and syntactic finiteness for supported algebras
type: theorem
---
Lemmas 56, 62, and 75 with revised Definition 6 as the algebra domain.
The completion bridge transfers finite recognition, while invariance of
a recognized language follows directly from invariance of its evaluation.
-/

namespace Lax369799.SupportedRecognition
open RankedSystems Algebras

axiom language_invariant {A B : RankedSet} (E : SupportedAlgebras.Algebra B)
    (hE : SupportedAlgebras.UnfoldInvariant E) (η : RankedMap A B) (F : Set (B 0))
    (L : Language A) (hL : SupportedAlgebras.Recognizes E η F L) : UnfoldInvariantLanguage L

axiom complement {A : RankedSet} (L : Language A) (h : SupportedAlgebras.Recognizable L) :
    SupportedAlgebras.Recognizable Lᶜ

axiom intersection {A : RankedSet} (L K : Language A)
    (hL : SupportedAlgebras.Recognizable L) (hK : SupportedAlgebras.Recognizable K) :
    SupportedAlgebras.Recognizable (L ∩ K)

axiom union {A : RankedSet} (L K : Language A)
    (hL : SupportedAlgebras.Recognizable L) (hK : SupportedAlgebras.Recognizable K) :
    SupportedAlgebras.Recognizable (L ∪ K)

axiom inverse_relabel {A B : RankedSet} (η : RankedMap A B) (L : Language B)
    (hL : SupportedAlgebras.Recognizable L) :
    SupportedAlgebras.Recognizable {S | relabelSystem η S ∈ L}

axiom projection {A B : RankedSet} (η : RankedMap A B)
    (hη : ∀ n, Function.Surjective (η n)) (L : Language A)
    (hL : SupportedAlgebras.Recognizable L) :
    SupportedAlgebras.Recognizable (RecognitionProjection.Projected η L)

axiom syntactic_rankwise_finite {A : RankedSet} (L : Language A)
    (hL : UnfoldInvariantLanguage L) (hrec : SupportedAlgebras.Recognizable L) :
    RankwiseFinite (FiniteContextualOrder.Carrier (FiniteAcceptance.Accepting L))

end Lax369799.SupportedRecognition
