import Lax369799.ModalAcceptanceGame

/-!
---
title: Small finite models for modal parity acceptance
type: theorem
---
If a modal acceptance game wins on a finite transition system, it wins
on a finite reachable system with at most as many vertices as the word
condition has states. Alternating simulations and positional strategies
supply the bound needed for the finite-search effectivity argument.
-/

namespace Lax369799.ModalSmallModels
open TransitionEncoding TransitionSystems UnfoldAutomata ParityWinningRegions

axiom small_model {P : Type} (M : UnfoldAutomaton (TransitionAlphabet P)) (S : TransitionSystem P)
    (h : Winning (ModalAcceptanceGame.game M S) true
      (ModalAcceptanceGame.position M.condition.initial S.initial)) :
    ∃ T : TransitionSystem P,T.size ≤ M.condition.states ∧
      Winning (ModalAcceptanceGame.game M T) true
        (ModalAcceptanceGame.position M.condition.initial T.initial)

end Lax369799.ModalSmallModels
