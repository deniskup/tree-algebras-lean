import Lax369799.RunWordCondition
import Lax369799Proofs.RunBranchObservations
import Lax369799Proofs.CombinedWordCondition

namespace Lax369799Proofs.RunWordCondition
set_option backward.isDefEq.respectTransparency false
open Lax369799
open RankedSystems (RankedSet System)
open FiniteContextualOrder FiniteAcceptance FiniteSyntacticAlgebra ExpandedSyntacticAlgebra
open UnfoldAutomata ExpandedTransitions

open Lax369799.RunWordCondition

private theorem decode_fold {A : RankedSet} (L : Algebras.Language A)
    [Fintype (Carrier (Accepting L) 1)] [Fintype (Carrier (Accepting L) 0)]
    (E : SyntacticAlgebra L)
    (w : List (Fin (Fintype.card (Carrier (Accepting L) 1))))
    (a : Fin (Fintype.card (Carrier (Accepting L) 0))) :
    (Fintype.equivFin (Carrier (Accepting L) 0)).symm (w.foldr (action L E) a) =
      FiniteBranchWords.value E.algebra
        (w.map (Fintype.equivFin (Carrier (Accepting L) 1)).symm)
        ((Fintype.equivFin (Carrier (Accepting L) 0)).symm a) := by
  induction w with
  | nil => rfl
  | cons b w ih =>
    simp only [List.foldr_cons, List.map_cons, FiniteBranchWords.value,
      action, Equiv.symm_apply_apply] at ih ⊢
    rw [ih]

/--
---
conclusion: Lax369799.RunWordCondition.finite_path_iff
---
Decoding commutes with the fold of encoded unary actions. The direct
path evaluation theorem identifies the resulting accepting value.
-/
theorem finite_path_iff {A : RankedSet} (L : Algebras.Language A)
    [Fintype (Carrier (Accepting L) 1)] [Fintype (Carrier (Accepting L) 0)]
    (E : SyntacticAlgebra L)
    (D : WordCondition (Fintype.card (Carrier (Accepting L) 1))
      (Fintype.card (Carrier (Accepting L) 0)))
    {S : System A 0} (r : Run (automaton L E (condition L E D)) S)
    {k : ℕ} (b : FiniteBranch S k) :
    (condition L E D).AcceptsFinite
      (List.ofFn (fun i => r.edgeType (b.vertex i.castSucc) (b.direction i)))
      (r.leafType (b.vertex (Fin.last k)) b.ends) ↔
      AcceptingClass (Accepting L)
        (E.algebra.eval 0 (RunBranchObservations.path L E (condition L E D) r.toLabelling b)) := by
  change (CombinedWordCondition.combine D (action L E) (finalCodes L)).AcceptsFinite _ _ ↔ _
  rw [CombinedWordCondition.finite_iff]
  change AcceptingClass (Accepting L) ((Fintype.equivFin (Carrier (Accepting L) 0)).symm _) ↔ _
  rw [decode_fold, RunBranchObservations.path_evaluation]
  simp only [List.map_ofFn, Function.comp_def, Run.toLabelling]

/--
---
conclusion: Lax369799.RunWordCondition.infinite_iff
---
The product word condition retains the supplied parity test.
-/
theorem infinite_iff {A : RankedSet} (L : Algebras.Language A)
    [Fintype (Carrier (Accepting L) 1)] [Fintype (Carrier (Accepting L) 0)]
    (E : SyntacticAlgebra L)
    (D : WordCondition (Fintype.card (Carrier (Accepting L) 1))
      (Fintype.card (Carrier (Accepting L) 0)))
    (w : ℕ → Fin (Fintype.card (Carrier (Accepting L) 1))) :
    (condition L E D).AcceptsInfinite w ↔ D.AcceptsInfinite w :=
  CombinedWordCondition.infinite_iff D _ _ w

end Lax369799Proofs.RunWordCondition
