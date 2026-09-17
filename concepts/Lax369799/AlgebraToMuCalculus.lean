import Lax369799.Algebras
import Lax369799.ModalMuCalculus
import Lax369799.TransitionEncoding

/-!
---
title: Bisimulation-invariant algebraic recognition implies mu-calculus definability
type: theorem
---
A bisimulation-invariant language over the transition alphabet recognised
by a rankwise-finite algebra is definable by a modal mu-calculus sentence
on its decoded transition systems. This is `thm:alg2mu` in Section 6.4.
-/

namespace Lax369799.AlgebraToMuCalculus
open RankedSystems Algebras TransitionEncoding

axiom algebra_to_mu {P : Type} [Finite P] (L : Language (TransitionAlphabet P))
    (hL : ∀ S T, RankedBisimilar S T → (S ∈ L ↔ T ∈ L))
    (hA : Recognizable L) :
    ∃ φ : ModalMuCalculus.Sentence P, ∀ S, S ∈ L ↔ ModalMuCalculus.Models (decode S) φ

end Lax369799.AlgebraToMuCalculus
