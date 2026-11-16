import Lax369799.AlgebraicBranchCondition
import Lax369799Proofs.AlgebraicOmegaWords
import Lax369799Proofs.CombinedWordCondition

namespace Lax369799Proofs.AlgebraicBranchCondition
open Lax369799
open RankedSystems (RankedSet)
open FiniteSyntacticAlgebra UnfoldAutomata

/--
---
conclusion: Lax369799.AlgebraicBranchCondition.exists_condition
---
Combine the linked-pair parity automaton with the finite evaluator. Its
second component records the composed action of the unary prefix on a
terminal nullary value.
-/
theorem exists_condition {A : RankedSet} (E : Algebra A) (F : Set (A 0))
    [Fintype (A 1)] [Fintype (A 0)] :
    ∃ D : WordCondition (Fintype.card (A 1)) (Fintype.card (A 0)),
      (∀ w a, D.AcceptsFinite w a ↔
        FiniteBranchWords.value E (w.map (Fintype.equivFin (A 1)).symm)
          ((Fintype.equivFin (A 0)).symm a) ∈ F) ∧
      (∀ w, D.AcceptsInfinite w ↔
        AlgebraicOmegaWords.Accepts E F (fun n => (Fintype.equivFin (A 1)).symm (w n))) := by
  classical
  let eu := Fintype.equivFin (A 1)
  let ez := Fintype.equivFin (A 0)
  let f := fun (b : Fin (Fintype.card (A 1))) (a : Fin (Fintype.card (A 0))) =>
    ez (FiniteBranchWords.act E (eu.symm b) (ez.symm a))
  let G : Set (Fin (Fintype.card (A 0))) := {a | ez.symm a ∈ F}
  obtain ⟨D, hD⟩ := AlgebraicOmegaWords.regular (z := Fintype.card (A 0)) E F
  refine ⟨CombinedWordCondition.combine D f G, ?_, fun w =>
    (CombinedWordCondition.infinite_iff D f G w).trans (hD w)⟩
  intro w a
  rw [CombinedWordCondition.finite_iff]
  have hv (w : List (Fin (Fintype.card (A 1)))) (a : Fin (Fintype.card (A 0))) :
      ez.symm (w.foldr f a) = FiniteBranchWords.value E (w.map eu.symm) (ez.symm a) := by
    induction w with
    | nil => rfl
    | cons b w ih =>
      simpa only [List.foldr_cons, List.map_cons, FiniteBranchWords.value, f,
        ez.symm_apply_apply] using congrArg (FiniteBranchWords.act E (eu.symm b)) ih
  exact Iff.of_eq (congrArg (· ∈ F) (hv w a))

end Lax369799Proofs.AlgebraicBranchCondition
