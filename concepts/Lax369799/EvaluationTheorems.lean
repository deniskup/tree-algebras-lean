import Lax369799.SetAlgebras

/-!
---
title: Evaluation of sums and contexts
type: theorem
---
Evaluation turns disjoint union into meet. Substituting a set-system has
the same value as substituting its evaluated atomic letter. Evaluation
in every context is monotone for the induced algebra order. These are
consequences of the unit, flattening, and morphism axioms used in the
normal-form and extremal-context arguments.
-/

namespace Lax369799.EvaluationTheorems
open RankedSystems Flattening SetAlgebras

axiom eval_sum {A : RankedSet} (E : SetAlgebra A) {n : ℕ} (S T : SetSystem A n) :
  E.eval n (sum S T) = meet E (E.eval n S) (E.eval n T)

axiom context_evaluation {A : RankedSet} (E : SetAlgebra A) {k n : ℕ}
    (C : SetContext A k n) (S : SetSystem A k) :
  E.eval n (plug C S) = E.eval n (plug C (atomic (E.eval k S)))

axiom context_monotone {A : RankedSet} (E : SetAlgebra A) {k n : ℕ}
    (C : SetContext A k n) (a b : A k) (h : Below E a b) :
  Below E (E.eval n (plug C (atomic a))) (E.eval n (plug C (atomic b)))

axiom relabel_monotone {A B : RankedSet} (E : SetAlgebra A)
    (f g : RankedMap B A) (h : ∀ r b, Below E (f r b) (g r b))
    {n : ℕ} (S : SetSystem B n) :
  Below E (E.eval n (relabel f S)) (E.eval n (relabel g S))

end Lax369799.EvaluationTheorems
