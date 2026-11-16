import Lax369799.AlgebraicOmegaWords
import Lax369799.CombinedWordCondition

/-!
---
title: A common condition for finite and infinite algebraic branch words
type: theorem
---
The word condition of Section 6.3 combines terminating-word evaluation
with the linked-pair condition on infinite words. Both conditions are
realized by one finite deterministic parity word automaton with final
states for terminating words.
-/

namespace Lax369799.AlgebraicBranchCondition
open RankedSystems (RankedSet)
open FiniteSyntacticAlgebra UnfoldAutomata

axiom exists_condition {A : RankedSet} (E : Algebra A) (F : Set (A 0))
    [Fintype (A 1)] [Fintype (A 0)] :
    ∃ D : WordCondition (Fintype.card (A 1)) (Fintype.card (A 0)),
      (∀ w a, D.AcceptsFinite w a ↔
        FiniteBranchWords.value E (w.map (Fintype.equivFin (A 1)).symm)
          ((Fintype.equivFin (A 0)).symm a) ∈ F) ∧
      (∀ w, D.AcceptsInfinite w ↔
        AlgebraicOmegaWords.Accepts E F (fun n => (Fintype.equivFin (A 1)).symm (w n)))

end Lax369799.AlgebraicBranchCondition
