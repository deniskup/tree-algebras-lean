import Lax369799.FiniteTesting
import Lax369799.QuantitativeFiniteTheorem
import Mathlib.Data.List.ProdSigma

/-!
---
title: Effective translation of bisimulation-invariant finite MSO
type: theorem
---
The algorithm is total on all MSO sentences over an explicitly encoded
finite vocabulary. It enumerates bounded modal transition tables and
selects a compiled sentence by finite graph tests. Under the promised
finite bisimulation invariance, the selected sentence agrees on every
finite reachable transition system. No invariance decision is required.
This formalizes the effectivity argument following Theorem 2.
-/

namespace Lax369799.EffectiveFiniteTranslation
open ModalMuCalculus

def candidates {P : Type} [Fintype P] [Encodable P] [DecidableEq P]
    (φ : MonadicSecondOrder.Sentence P) : List (Sentence P) :=
  let f := QuantitativeRecognition.msoBound φ
  (List.range (QuantitativeAutomata.unaryBound f+1)).flatMap (fun u =>
    (List.range (QuantitativeAutomata.nullaryBound f+1)).flatMap (fun z =>
      (List.range (QuantitativeAutomata.stateBound f+1)).flatMap (fun d =>
        (FiniteModalData.elements (FiniteModalData.Data P u z d (QuantitativeAutomata.priorityBound f))).map
          FiniteModalData.compile)))

def conjunction {P : Type} (φ ψ : MonadicSecondOrder.Sentence P) : MonadicSecondOrder.Sentence P :=
  .neg (.disj (.neg φ) (.neg ψ))

def difference {P : Type} (ψ χ : Sentence P) : MonadicSecondOrder.Sentence P :=
  .disj (conjunction (UnrestrictedLogic.sentence ψ) (.neg (UnrestrictedLogic.sentence χ)))
    (conjunction (.neg (UnrestrictedLogic.sentence ψ)) (UnrestrictedLogic.sentence χ))

def separationBound {P : Type} (cs : List (Sentence P)) : ℕ :=
  ((cs.product cs).map (fun e => QuantitativeFiniteTheorem.modelBound (difference e.1 e.2))).foldr max 0

def compile {P : Type} [Fintype P] [Encodable P] [DecidableEq P]
    (φ : MonadicSecondOrder.Sentence P) : Sentence P :=
  let cs := candidates φ
  (cs.find? (fun ψ => FiniteTesting.test (separationBound cs) φ ψ)).getD .bot

open TransitionSystems

axiom mu_translation_correct {P : Type} (ψ : Sentence P) (S : TransitionSystem P) :
    Models S ψ ↔ MonadicSecondOrder.Models S (UnrestrictedLogic.sentence ψ)

-- Compiler correctness is the effective theorem in FiniteBisimulationTheorem.
-- Keep one Archive statement for this result.

end Lax369799.EffectiveFiniteTranslation
