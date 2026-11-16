import Lax369799.QuantitativeProfiles
import Lax369799.QuantitativeWordConditions
import Lax369799.BisimAutomatonTheorem

/-!
---
title: Quantitative automata for the finite bisimulation theorem
type: theorem
---
A bound for the recognizing algebra gives explicit bounds for the unary
and nullary types, word states and priorities of the equivalent clone
automaton. The infinite stabilization defining its transition table does
not change any of these finite bounds.
-/

namespace Lax369799.QuantitativeAutomata

def unaryBound (f : ℕ → ℕ) := QuantitativeProfiles.quotientBound f 1
def nullaryBound (f : ℕ → ℕ) := QuantitativeProfiles.quotientBound f 0

def stateBound (f : ℕ → ℕ) :=
  QuantitativeWordConditions.stateBound (unaryBound f) (nullaryBound f)

def priorityBound (f : ℕ → ℕ) :=
  QuantitativeWordConditions.priorityBound (unaryBound f)

open TransitionEncoding UnfoldAutomata

axiom automaton_bound {P : Type} [Finite P]
    (L : Algebras.Language (TransitionAlphabet P))
    (hL : ∀ S T,RankedBisimilar S T → (S ∈ L ↔ T ∈ L))
    (f : ℕ → ℕ) (hA : QuantitativeRecognition.Bound f L) :
    ∃ M : UnfoldAutomaton (TransitionAlphabet P),
      BisimAutomata.IsBisimAutomaton M ∧ Recognizes M L ∧
      M.unary ≤ unaryBound f ∧ M.nullary ≤ nullaryBound f ∧
      M.condition.states ≤ stateBound f ∧ (∀ q,M.condition.priority q ≤ priorityBound f)

end Lax369799.QuantitativeAutomata