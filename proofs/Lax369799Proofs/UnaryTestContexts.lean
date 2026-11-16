import Lax369799.UnaryTestContexts
import Lax369799Proofs.ClosedUnaryLift
import Lax369799Proofs.SplitExtremal

namespace Lax369799Proofs.UnaryTestContexts
open Lax369799.RankedSystems (RankedSet)
open Lax369799.FinitePresentations Lax369799.FiniteSyntacticAlgebra
open Lax369799.FiniteContextualOrder Lax369799.FiniteAcceptance Lax369799.UnaryTestContexts

private theorem meet_distribute {A : RankedSet} (L : Lax369799.Algebras.Language A)
    (E : Algebra (Carrier (Accepting L)))
    (hE : ∀ n (S : FiniteSystem (FiniteSystem A) n),
      E.eval n (relabel (quotientMap (Accepting L)) S) = quotientMap (Accepting L) n (flatten S))
    {n : ℕ} (p c d : Carrier (Accepting L) n) :
    sumValue E p (sumValue E c d) = sumValue E (sumValue E p c) (sumValue E p d) := by
  have h (w : Carrier (Accepting L) n) :
      ClassBelow (Accepting L) w (sumValue E p (sumValue E c d)) ↔
      ClassBelow (Accepting L) w (sumValue E (sumValue E p c) (sumValue E p d)) := by
    simp only [FiniteOrderedAlgebra.sum_value_meet L E hE]
    tauto
  have ho := FiniteContextualOrder.class_order (Accepting L) n
  exact ho.2.1 _ _ ((h _).mp (ho.1 _)) ((h _).mpr (ho.1 _))

/--
---
conclusion: Lax369799.UnaryTestContexts.data_sum
---
Both marked and unmarked lifts preserve sums. Duplicating the fixed
planted prefix is absorbed by idempotence of the contextual meet.
-/
theorem data_sum {A : RankedSet} (L : Lax369799.Algebras.Language A)
    (E : Algebra (Carrier (Accepting L)))
    (hE : ∀ n (S : FiniteSystem (FiniteSystem A) n),
      E.eval n (relabel (quotientMap (Accepting L)) S) = quotientMap (Accepting L) n (flatten S))
    (root : Prop) (t : Carrier (Accepting L) 1) (c d : Carrier (Accepting L) 0) :
    data E root t (sumValue E c d) =
      Lax369799.SplitExtremal.meetData E (data E root t c) (data E root t d) := by
  apply Prod.ext
  · change (⟨root, ∅⟩ : Lax369799.ExtremalContexts.Boundary 1) = ⟨root ∨ root, ∅ ∪ ∅⟩
    congr 1
    · exact propext (by tauto)
    · simp
  · funext i
    change sumValue E _ (Lax369799.ClosedUnaryLift.value E (i == 1) (sumValue E c d)) = _
    rw [ClosedUnaryLift.preserves_sum]
    exact meet_distribute L E hE _ _ _

end Lax369799Proofs.UnaryTestContexts
