import Lax369799.RunBranchObservations
import Lax369799.CombinedWordCondition

/-!
---
title: The terminating-word condition for algebraic runs
type: theorem
---
Encode unary actions and the accepting nullary values as finite types.
Combining their finite-word evaluator with a parity condition tests finite
run paths exactly by algebraic evaluation and retains the given infinite
word condition.
-/
namespace Lax369799.RunWordCondition
open RankedSystems (RankedSet System)
open FiniteContextualOrder FiniteAcceptance FiniteSyntacticAlgebra ExpandedSyntacticAlgebra
open UnfoldAutomata ExpandedTransitions

noncomputable def action {A : RankedSet} (L : Algebras.Language A)
    [Fintype (Carrier (Accepting L) 1)] [Fintype (Carrier (Accepting L) 0)]
    (E : SyntacticAlgebra L) :
    Fin (Fintype.card (Carrier (Accepting L) 1)) →
    Fin (Fintype.card (Carrier (Accepting L) 0)) → Fin (Fintype.card (Carrier (Accepting L) 0)) :=
  fun b a => (Fintype.equivFin (Carrier (Accepting L) 0)) (FiniteBranchWords.act E.algebra
    ((Fintype.equivFin (Carrier (Accepting L) 1)).symm b)
    ((Fintype.equivFin (Carrier (Accepting L) 0)).symm a))

noncomputable def finalCodes {A : RankedSet} (L : Algebras.Language A)
    [Fintype (Carrier (Accepting L) 0)] : Set (Fin (Fintype.card (Carrier (Accepting L) 0))) :=
  {a | AcceptingClass (Accepting L) ((Fintype.equivFin (Carrier (Accepting L) 0)).symm a)}

noncomputable def condition {A : RankedSet} (L : Algebras.Language A)
    [Fintype (Carrier (Accepting L) 1)] [Fintype (Carrier (Accepting L) 0)]
    (E : SyntacticAlgebra L)
    (D : WordCondition (Fintype.card (Carrier (Accepting L) 1))
      (Fintype.card (Carrier (Accepting L) 0))) :=
  CombinedWordCondition.combine D (action L E) (finalCodes L)


axiom finite_path_iff {A : RankedSet} (L : Algebras.Language A)
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
        (E.algebra.eval 0 (RunBranchObservations.path L E (condition L E D) r.toLabelling b))

axiom infinite_iff {A : RankedSet} (L : Algebras.Language A)
    [Fintype (Carrier (Accepting L) 1)] [Fintype (Carrier (Accepting L) 0)]
    (E : SyntacticAlgebra L)
    (D : WordCondition (Fintype.card (Carrier (Accepting L) 1))
      (Fintype.card (Carrier (Accepting L) 0)))
    (w : ℕ → Fin (Fintype.card (Carrier (Accepting L) 1))) :
    (condition L E D).AcceptsInfinite w ↔ D.AcceptsInfinite w

end Lax369799.RunWordCondition
