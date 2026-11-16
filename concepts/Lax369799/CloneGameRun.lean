import Lax369799.AutomatonRunGame

/-!
---
title: Realizing winning clone-automaton strategies
type: theorem
---
Duplicate transition components to cover every permitted successor of a
winning marking. The reachable part of this finite strategy construction
is bisimilar to the input system and carries an accepting automaton run.
-/

namespace Lax369799.CloneGameRun
open TransitionEncoding TransitionSystems UnfoldAutomata ModalAcceptanceGame

axiom winning_run {P : Type} (M : UnfoldAutomaton (TransitionAlphabet P))
    (hM : BisimAutomata.IsBisimAutomaton M) (S : TransitionSystem P)
    (hwin : ParityWinningRegions.Winning (game M S) true
      (position M.condition.initial S.initial)) :
    ∃ U : RankedSystems.System (TransitionAlphabet P) 0,
      Bisimilar (decode U) S ∧ ∃ r : Run M U, r.Accepting

end Lax369799.CloneGameRun
