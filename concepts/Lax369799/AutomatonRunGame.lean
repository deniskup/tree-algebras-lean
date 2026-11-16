import Lax369799.ModalAcceptanceGame

/-!
---
title: Accepting runs and modal game plays
type: theorem
---
Every accepting run supplies winning modal choices. Finite branches use
the final-state test, while infinite branches use the parity condition.
Inserting zero-priority marking positions between word positions does
not alter the acceptance condition.
-/

namespace Lax369799.AutomatonRunGame
open TransitionEncoding TransitionSystems UnfoldAutomata ModalAcceptanceGame

axiom parity_interleave {P : Type} (M : UnfoldAutomaton (TransitionAlphabet P))
    (S : TransitionSystem P) (w : ℕ → Fin M.unary) (p : ℕ → Vertex M S)
    (he : ∀ n, (game M S).priority (p (2*n)) =
      ceiling M.condition - M.condition.priority (M.condition.run w n))
    (ho : ∀ n, (game M S).priority (p (2*n+1)) = 0) :
    M.condition.AcceptsInfinite w ↔ (game M S).EveWins p

axiom run_winning {P : Type} (M : UnfoldAutomaton (TransitionAlphabet P))
    {S : RankedSystems.System (TransitionAlphabet P) 0} (r : Run M S) (hr : r.Accepting) :
    ParityWinningRegions.Winning (game M (decode S)) true
      (position M.condition.initial (decode S).initial)

end Lax369799.AutomatonRunGame
