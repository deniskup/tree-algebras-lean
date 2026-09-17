import Lax369799.FiniteSyntacticAlgebra
import Lax369799Proofs.FiniteContextualOrder
import Mathlib.Data.Quot

namespace Lax369799Proofs.FiniteSyntacticAlgebra
open Lax369799.RankedSystems (RankedSet RankedMap)
open Lax369799.FinitePresentations Lax369799.FiniteContextualOrder Lax369799.FiniteSyntacticAlgebra

private def contextualSetoid {A : RankedSet} (F : ClosedProperty A) (n : ℕ) :
    Setoid (FiniteSystem A n) where
  r := Equivalent F
  iseqv := {
    refl := fun _ => ⟨fun _ => id, fun _ => id⟩
    symm := fun h => h.symm
    trans := fun h g => ⟨fun C hc => g.1 C (h.1 C hc), fun C hc => h.2 C (g.2 C hc)⟩ }

private theorem quotient_exact {A : RankedSet} (F : ClosedProperty A) {n : ℕ}
    (S T : FiniteSystem A n) (h : quotientMap F n S = quotientMap F n T) : Equivalent F S T :=
  @Quotient.exact _ (contextualSetoid F n) _ _ h

private theorem quotient_iso {A : RankedSet} (F : ClosedProperty A) (hF : IsoInvariant F)
    {n : ℕ} (S T : FiniteSystem A n) (h : Isomorphic S T) :
    quotientMap F n S = quotientMap F n T :=
  Quot.sound (FiniteContextualOrder.contextual_iso F hF S T h)

private noncomputable def representative {A : RankedSet} (F : ClosedProperty A) :
    RankedMap (Carrier F) (FiniteSystem A) := fun _ q => q.out

private noncomputable def evaluate {A : RankedSet} (F : ClosedProperty A) :
    ∀ n, FiniteSystem (Carrier F) n → Carrier F n :=
  fun n S => quotientMap F n (flatten (relabel (representative F) S))

private theorem evaluate_representatives {A : RankedSet} (F : ClosedProperty A) (hF : IsoInvariant F)
    (n : ℕ) (S : FiniteSystem (FiniteSystem A) n) :
    evaluate F n (relabel (quotientMap F) S) = quotientMap F n (flatten S) := by
  apply Quot.sound
  let q := fun v : S.Vertex => representative F (S.graph.label v).1
    (quotientMap F (S.graph.label v).1 (S.graph.label v).2)
  let r := fun v : S.Vertex => (S.graph.label v).2
  have h v : Equivalent F (q v) (r v) := quotient_exact F _ _
    (Quot.out_eq (quotientMap F (S.graph.label v).1 (S.graph.label v).2))
  exact ⟨FiniteContextualOrder.flatten_monotone F hF S q r (fun v => (h v).1),
    FiniteContextualOrder.flatten_monotone F hF S r q (fun v => (h v).2)⟩

private theorem evaluate_unit {A : RankedSet} (F : ClosedProperty A) (hF : IsoInvariant F)
    (n : ℕ) (a : Carrier F n) : evaluate F n (atomic a) = a := by
  exact (quotient_iso F hF _ _ (UntrimmedFlattening.outer_atomic (representative F n a))).trans
    (Quot.out_eq a)

private theorem evaluate_iso {A : RankedSet} (F : ClosedProperty A) (hF : IsoInvariant F)
    (n : ℕ) (S T : FiniteSystem (Carrier F) n) (h : Isomorphic S T) :
    evaluate F n S = evaluate F n T := by
  obtain ⟨f⟩ := h
  exact quotient_iso F hF _ _ (UntrimmedFlattening.flatten_iso _ _
    ⟨UntrimmedFlattening.relabelIso (representative F) f⟩)

private theorem evaluate_associative {A : RankedSet} (F : ClosedProperty A) (hF : IsoInvariant F)
    (n : ℕ) (S : FiniteSystem (FiniteSystem (Carrier F)) n) :
    evaluate F n (relabel (evaluate F) S) = evaluate F n (flatten S) := by
  let g : RankedMap (FiniteSystem (Carrier F)) (FiniteSystem (FiniteSystem A)) :=
    fun _ U => relabel (representative F) U
  calc
    evaluate F n (relabel (evaluate F) S) =
        quotientMap F n (flatten (relabel (fun r U => flatten (g r U)) S)) :=
      evaluate_representatives F hF n (relabel (fun r U => flatten (g r U)) S)
    _ = quotientMap F n (flatten (flatten (relabel g S))) :=
      (quotient_iso F hF _ _ (UntrimmedFlattening.flatten_associative (relabel g S))).symm
    _ = evaluate F n (flatten S) := by
      unfold evaluate
      rw [UntrimmedFlattening.flatten_natural]

/--
---
conclusion: Lax369799.FiniteSyntacticAlgebra.contextual_algebra
---
Choose representatives, flatten, and take the contextual equivalence
class. Pointwise contextual congruence makes the result independent of
the representatives. The unpruned monad laws give the algebra laws.
-/
theorem contextual_algebra {A : RankedSet} (F : ClosedProperty A) (hF : IsoInvariant F) :
    ∃ E : Algebra (Carrier F), ∀ n (S : FiniteSystem (FiniteSystem A) n),
      E.eval n (relabel (quotientMap F) S) = quotientMap F n (flatten S) := by
  exact ⟨{
    eval := evaluate F
    unit := evaluate_unit F hF
    associative := evaluate_associative F hF
    isomorphic := evaluate_iso F hF }, evaluate_representatives F hF⟩

/--
---
conclusion: Lax369799.FiniteSyntacticAlgebra.contextual_recognition
---
The identity context makes the closed property constant on contextual
classes. Evaluating the atomic class of each letter returns the class of
the original presentation, by the inner atomic unit law.
-/
theorem contextual_recognition {A : RankedSet} (F : ClosedProperty A) (hF : IsoInvariant F)
    (E : Algebra (Carrier F))
    (hE : ∀ n (S : FiniteSystem (FiniteSystem A) n),
      E.eval n (relabel (quotientMap F) S) = quotientMap F n (flatten S)) :
    ∃ P : Set (Carrier F 0), ∀ S : FiniteSystem A 0,
      E.eval 0 (relabel (fun r a => quotientMap F r (atomic a)) S) ∈ P ↔ S ∈ F := by
  let P : Set (Carrier F 0) := fun q => Quot.lift (fun S => S ∈ F) (by
    intro S T h
    exact propext ⟨FiniteContextualOrder.contextual_acceptance F hF S T h.1,
      FiniteContextualOrder.contextual_acceptance F hF T S h.2⟩) q
  refine ⟨P, fun S => ?_⟩
  have he := hE 0 (relabel (fun _ a => atomic a) S)
  change E.eval 0 (relabel (fun r a => quotientMap F r (atomic a)) S) =
    quotientMap F 0 (flatten (relabel (fun _ a => atomic a) S)) at he
  rw [he]
  exact hF _ _ (UntrimmedFlattening.inner_atomic S)

end Lax369799Proofs.FiniteSyntacticAlgebra
