import Lax369799.QuantitativeAutomata
import Lax369799.ModalSmallModels
import Lax369799.MonadicSecondOrder

/-!
---
title: A computable finite-model bound under bisimulation invariance
type: theorem
---
The quantitative construction of Theorem 2 gives a bounded modal
certificate. Its small-model property provides a syntax-computed bound
for every nonempty bisimulation-invariant MSO sentence on finite systems.
-/

namespace Lax369799.QuantitativeFiniteTheorem

def modelBound {P : Type} (φ : MonadicSecondOrder.Sentence P) : ℕ :=
  QuantitativeAutomata.stateBound (QuantitativeRecognition.msoBound φ)

open TransitionEncoding TransitionSystems UnfoldAutomata ParityWinningRegions

axiom modal_certificate {P : Type} [Finite P] (φ : MonadicSecondOrder.Sentence P)
    (hφ : BisimulationInvariant {S | MonadicSecondOrder.Models S φ}) :
    ∃ M : UnfoldAutomaton (TransitionAlphabet P),
      M.unary ≤ QuantitativeAutomata.unaryBound (QuantitativeRecognition.msoBound φ) ∧
      M.nullary ≤ QuantitativeAutomata.nullaryBound (QuantitativeRecognition.msoBound φ) ∧
      M.condition.states ≤ modelBound φ ∧
      (∀ q,M.condition.priority q ≤ QuantitativeAutomata.priorityBound (QuantitativeRecognition.msoBound φ)) ∧
      ∀ S,MonadicSecondOrder.Models S φ ↔ Winning (ModalAcceptanceGame.game M S) true
        (ModalAcceptanceGame.position M.condition.initial S.initial)

open TransitionEncoding TransitionSystems UnfoldAutomata ParityWinningRegions

axiom nonempty_bound {P : Type} [Finite P] (φ : MonadicSecondOrder.Sentence P)
    (hφ : BisimulationInvariant {S | MonadicSecondOrder.Models S φ})
    (h : ∃ S,MonadicSecondOrder.Models S φ) :
    ∃ T : TransitionSystem P,T.size ≤ modelBound φ ∧ MonadicSecondOrder.Models T φ

end Lax369799.QuantitativeFiniteTheorem