import Lax369799.ChoicePreservingUnary

namespace Lax369799Proofs.ChoicePreservingUnary
open Lax369799.RankedSystems (RankedSet)
open Lax369799.FiniteSyntacticAlgebra Lax369799.FiniteBranchWords Lax369799.ChoicePreservingUnary

/--
---
conclusion: Lax369799.ChoicePreservingUnary.word_preserves_choices
---
Choice preservation is closed under composition of unary actions.
-/
theorem word_preserves_choices {A : RankedSet} (E : Algebra A)
    (w : List (A 1)) (hw : ∀ b ∈ w, PreservesChoices E b) (c d : A 0) :
    value E w (sumValue E c d) = sumValue E (value E w c) (value E w d) := by
  induction w with
  | nil => rfl
  | cons b w ih =>
    have hb := hw b (by simp)
    have ht : ∀ a ∈ w, PreservesChoices E a := fun a ha => hw a (List.mem_cons_of_mem _ ha)
    change act E b (value E w (sumValue E c d)) = _
    rw [ih ht]
    exact hb _ _

private theorem prefix_test {A : RankedSet} (E : Algebra A) (F : Set (A 0))
    (hF : ∀ c d, sumValue E c d ∈ F ↔ c ∈ F ∧ d ∈ F)
    (t : Expression A) (ht : t.Eligible E)
    (w : List (A 1)) (hw : ∀ b ∈ w, PreservesChoices E b) :
    value E w (t.eval E) ∈ F ↔ ∀ p ∈ t.paths, value E (w ++ p.1) p.2 ∈ F := by
  induction t generalizing w with
  | leaf a => simp [Expression.eval, Expression.paths]
  | choice s t ihs iht =>
    change value E w (sumValue E (s.eval E) (t.eval E)) ∈ F ↔ _
    rw [word_preserves_choices E w hw, hF, ihs ht.1 w hw, iht ht.2 w hw]
    simp only [Expression.paths, List.mem_append, or_imp, forall_and]
  | step b t ih =>
    have hw' : ∀ a ∈ w ++ [b], PreservesChoices E a := by
      intro a ha
      rcases List.mem_append.mp ha with ha | ha
      · exact hw a ha
      · have he : a = b := List.mem_singleton.mp ha
        subst a
        exact ht.1
    have hv : value E w ((Expression.step b t).eval E) = value E (w ++ [b]) (t.eval E) := by
      simp only [value, Expression.eval, List.foldr_append, List.foldr_cons, List.foldr_nil]
    rw [hv, ih ht.2 (w ++ [b]) hw']
    simp only [Expression.paths, List.mem_map, forall_exists_index, and_imp,
      forall_apply_eq_imp_iff₂, List.append_assoc, List.singleton_append]

/--
---
conclusion: Lax369799.ChoicePreservingUnary.finite_branch_test
---
Push each eligible unary prefix through choices. The accepting set tests
a choice by testing both summands, leaving precisely the finite paths.
-/
theorem finite_branch_test {A : RankedSet} (E : Algebra A) (F : Set (A 0))
    (hF : ∀ c d, sumValue E c d ∈ F ↔ c ∈ F ∧ d ∈ F)
    (t : Expression A) (ht : t.Eligible E) :
    t.eval E ∈ F ↔ ∀ p ∈ t.paths, value E p.1 p.2 ∈ F := by
  simpa only [value, List.foldr_nil, List.nil_append] using
    prefix_test E F hF t ht [] (by simp)

/--
---
conclusion: Lax369799.ChoicePreservingUnary.finite_types
---
Restricting a finite unary sort to eligible types preserves finiteness.
-/
theorem finite_types {A : RankedSet} (E : Algebra A) [Finite (A 1)] : Finite (TypeSet E) := by
  unfold TypeSet
  infer_instance

end Lax369799Proofs.ChoicePreservingUnary
