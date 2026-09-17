import Lax369799.EvaluationTheorems
import Lax369799Proofs.ContextCongruence
import Lax369799Proofs.SumEvaluation

namespace Lax369799Proofs.Evaluation
open Lax369799.RankedSystems Lax369799.Morphisms Lax369799.Flattening Lax369799.SetAlgebras
open Lax369799Proofs.Pullbacks Lax369799Proofs.MorphismTheorems

private theorem relabel_congr {A B : RankedSet} {n : ℕ} (S : SetSystem A n)
    (f g : RankedMap A B) (h : ∀ r a, f r a = g r a) : relabel f S = relabel g S := by
  have he : f = g := funext (fun r => funext (h r))
  rw [he]

/--
---
conclusion: Lax369799.EvaluationTheorems.context_evaluation
---
Use associativity to evaluate the labels before flattening. The unit
axiom gives the same labels after replacing the argument by its value.
-/
theorem context_evaluation {A : RankedSet} (E : SetAlgebra A) {k n : ℕ}
    (C : SetContext A k n) (S : SetSystem A k) :
    E.eval n (plug C S) = E.eval n (plug C (atomic (E.eval k S))) := by
  rw [plug, plug, ← E.associative, ← E.associative]
  apply congrArg (E.eval n)
  change relabel (fun r a => E.eval r (substitution S r a)) C.system =
    relabel (fun r a => E.eval r (substitution (atomic (E.eval k S)) r a)) C.system
  apply relabel_congr
  intro r a
  cases a with
  | inl a => rfl
  | inr h =>
    obtain ⟨h⟩ := h
    subst r
    exact (E.unit k (E.eval k S)).symm

private noncomputable def includeRight {A : RankedSet} {n : ℕ} (S T : SetSystem A n) :
    Morphism T (sum S T) :=
  lift (T := SumEvaluation.sumGraph S T) {
    toFun := Sum.inr
    initial := fun _ h => h
    root := fun _ h => h
    label := fun _ => rfl
    edge := fun _ _ t h => ⟨t, h, rfl⟩ }

private noncomputable def plug_morphism {A : RankedSet} {k n : ℕ} (C : SetContext A k n)
    {S T : SetSystem A k} (f : Morphism S T) : Morphism (plug C S) (plug C T) := by
  apply ContextCongruence.flatten_label_morphism C.system (substitution S) (substitution T)
  intro r a
  cases a with
  | inl a => exact identity (atomic a)
  | inr h =>
    obtain ⟨h⟩ := h
    subst r
    exact f

/--
---
conclusion: Lax369799.EvaluationTheorems.context_monotone
---
Insert the right summand into the sum of the two atomic arguments.
The induced morphism of plugged contexts reverses evaluation order;
the assumed meet equality then identifies the sum's value with a.
-/
theorem context_monotone {A : RankedSet} (E : SetAlgebra A) {k n : ℕ}
    (C : SetContext A k n) (a b : A k) (h : Below E a b) :
    Below E (E.eval n (plug C (atomic a))) (E.eval n (plug C (atomic b))) := by
  have hm := E.morphism n (plug C (atomic b)) (plug C (sum (atomic a) (atomic b)))
    ⟨plug_morphism C (includeRight (atomic a) (atomic b))⟩
  rw [context_evaluation E C (sum (atomic a) (atomic b))] at hm
  change E.eval k (sum (atomic a) (atomic b)) = a at h
  rw [h] at hm
  exact hm

end Lax369799Proofs.Evaluation
