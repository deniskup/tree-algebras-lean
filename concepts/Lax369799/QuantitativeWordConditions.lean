import Lax369799.QuantitativeDeterminization
import Lax369799.AlgebraicBranchCondition

/-!
---
title: Computable bounds for the algebraic branch automaton
type: theorem
---
The linked-pair automaton stores three elements of the unary monoid and
two flags. Determinization and the finite-word evaluator give explicit
state and priority bounds from the unary and nullary sort bounds.
-/

namespace Lax369799.QuantitativeWordConditions

def buchiBound (u : ℕ) : ℕ := 4*(u+1)^3

def stateBound (u z : ℕ) : ℕ :=
  QuantitativeDeterminization.stateBound (buchiBound u) * (z^z+z+1)

def priorityBound (u : ℕ) : ℕ :=
  QuantitativeDeterminization.priorityBound (buchiBound u)

open UnfoldAutomata

axiom exists_condition {A : RankedSystems.RankedSet} (E : FiniteSyntacticAlgebra.Algebra A)
    (F : Set (A 0)) [Fintype (A 1)] [Fintype (A 0)]
    (u z : ℕ) (hu : Fintype.card (A 1) ≤ u) (hz : Fintype.card (A 0) ≤ z) :
    ∃ D : WordCondition (Fintype.card (A 1)) (Fintype.card (A 0)),
      (∀ w a,D.AcceptsFinite w a ↔ FiniteBranchWords.value E
        (w.map (Fintype.equivFin (A 1)).symm) ((Fintype.equivFin (A 0)).symm a) ∈ F) ∧
      (∀ w,D.AcceptsInfinite w ↔ AlgebraicOmegaWords.Accepts E F
        (fun n => (Fintype.equivFin (A 1)).symm (w n))) ∧
      D.states ≤ stateBound u z ∧ (∀ q,D.priority q ≤ priorityBound u)

end Lax369799.QuantitativeWordConditions