import Lax369799.FiniteSyntacticAlgebra
import Lax369799Proofs.FiniteContextualOrder
import Mathlib.Data.Quot
import Lax369799Proofs.FiniteSums

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

private theorem relabel_representatives {A : RankedSet} (F : ClosedProperty A)
    {n : ℕ} (S : FiniteSystem (Carrier F) n) :
    relabel (quotientMap F) (relabel (representative F) S) = S := by
  dsimp only [relabel]
  congr 1
  congr 1
  funext v
  exact (congrArg (Sigma.mk (S.graph.label v).1) (Quot.out_eq (S.graph.label v).2)).trans
    (Sigma.eta (S.graph.label v))

private theorem evaluate_unique {A : RankedSet} (F : ClosedProperty A)
    (E : Algebra (Carrier F))
    (hE : ∀ n (S : FiniteSystem (FiniteSystem A) n),
      E.eval n (relabel (quotientMap F) S) = quotientMap F n (flatten S))
    (n : ℕ) (S : FiniteSystem (Carrier F) n) : E.eval n S = evaluate F n S := by
  have h := hE n (relabel (representative F) S)
  rw [relabel_representatives F S] at h
  exact h

theorem evaluation_by_representatives {A : RankedSet} (F : ClosedProperty A)
    (E : Algebra (Carrier F))
    (hE : ∀ n (S : FiniteSystem (FiniteSystem A) n),
      E.eval n (relabel (quotientMap F) S) = quotientMap F n (flatten S))
    {n : ℕ} (S : FiniteSystem (Carrier F) n) :
    E.eval n S = quotientMap F n (flatten (relabel (fun _ a => a.out) S)) :=
  evaluate_unique F E hE n S

/--
---
conclusion: Lax369799.FiniteSyntacticAlgebra.evaluation_monotone
---
Choose representatives of the ordered labels. The quotient order is their
contextual preorder, so simultaneous flattening monotonicity applies.
-/
theorem evaluation_monotone {A B : RankedSet} (F : ClosedProperty A) (hF : IsoInvariant F)
    (E : Algebra (Carrier F))
    (hE : ∀ n (S : FiniteSystem (FiniteSystem A) n),
      E.eval n (relabel (quotientMap F) S) = quotientMap F n (flatten S))
    {n : ℕ} (P : FiniteSystem B n)
    (q r : ∀ v : P.Vertex, Carrier F (P.graph.label v).1)
    (h : ∀ v, ClassBelow F (q v) (r v)) :
    ClassBelow F (E.eval n (withLabels P q)) (E.eval n (withLabels P r)) := by
  rw [evaluate_unique F E hE, evaluate_unique F E hE]
  apply FiniteContextualOrder.flatten_monotone F hF P
    (fun v => representative F _ (q v)) (fun v => representative F _ (r v))
  intro v
  have hv := h v
  rw [← Quot.out_eq (q v), ← Quot.out_eq (r v)] at hv
  exact hv

/--
---
conclusion: Lax369799.FiniteSyntacticAlgebra.accepting_classes
---
Acceptance is constant on contextual classes. The identity-context test
also makes the accepting classes upward closed in the contextual order.
-/
theorem accepting_classes {A : RankedSet} (F : ClosedProperty A) (hF : IsoInvariant F) :
    (∀ S, AcceptingClass F (quotientMap F 0 S) ↔ S ∈ F) ∧
    (∀ a b, AcceptingClass F a → ClassBelow F a b → AcceptingClass F b) := by
  have hq (S : FiniteSystem A 0) : AcceptingClass F (quotientMap F 0 S) ↔ S ∈ F := by
    constructor
    · rintro ⟨T, ht, hT⟩
      exact FiniteContextualOrder.contextual_acceptance F hF T S (quotient_exact F T S ht).1 hT
    · exact fun h => ⟨S, rfl, h⟩
  refine ⟨hq, ?_⟩
  intro a b
  induction a using Quot.inductionOn with
  | h S =>
    induction b using Quot.inductionOn with
    | h T =>
      intro hS hST
      exact (hq T).mpr (FiniteContextualOrder.contextual_acceptance F hF S T hST ((hq S).mp hS))

/--
---
conclusion: Lax369799.FiniteSyntacticAlgebra.sum_value
---
Evaluate the binary pattern of the two presentations. Its flattening is
their disjoint union, and quotient evaluation commutes with flattening.
-/
theorem sum_value {A : RankedSet} (F : ClosedProperty A) (hF : IsoInvariant F)
    (E : Algebra (Carrier F))
    (hE : ∀ n (S : FiniteSystem (FiniteSystem A) n),
      E.eval n (relabel (quotientMap F) S) = quotientMap F n (flatten S))
    {n : ℕ} (S T : FiniteSystem A n) :
    sumValue E (quotientMap F n S) (quotientMap F n T) = quotientMap F n (sum S T) := by
  have he : relabel (quotientMap F) (binary S T) =
      binary (quotientMap F n S) (quotientMap F n T) := by
    dsimp only [relabel, binary]
    congr 1
    congr 1
    funext v
    fin_cases v <;> rfl
  change E.eval n (binary _ _) = _
  rw [← he, hE]
  exact quotient_iso F hF _ _ (FiniteSums.flatten_binary S T)

/--
---
conclusion: Lax369799.FiniteSyntacticAlgebra.accepting_sum_value
---
Closure of the closed property under disjoint union transfers to the
binary sum operation on its contextual quotient.
-/
theorem accepting_sum_value {A : RankedSet} (F : ClosedProperty A) (hF : IsoInvariant F)
    (hSum : ∀ S T, S ∈ F → T ∈ F → sum S T ∈ F)
    (E : Algebra (Carrier F))
    (hE : ∀ n (S : FiniteSystem (FiniteSystem A) n),
      E.eval n (relabel (quotientMap F) S) = quotientMap F n (flatten S))
    (a b : Carrier F 0) :
    AcceptingClass F a → AcceptingClass F b → AcceptingClass F (sumValue E a b) := by
  induction a using Quot.inductionOn with
  | h S =>
    induction b using Quot.inductionOn with
    | h T =>
      intro hS hT
      have ha := (accepting_classes F hF).1
      have hST : AcceptingClass F (quotientMap F 0 (sum S T)) :=
        (ha _).mpr (hSum S T ((ha S).mp hS) ((ha T).mp hT))
      exact Eq.mpr (congrArg (AcceptingClass F) (sum_value F hF E hE S T)) hST

end Lax369799Proofs.FiniteSyntacticAlgebra
