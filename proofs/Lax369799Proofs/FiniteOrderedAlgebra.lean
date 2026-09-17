import Lax369799.FiniteOrderedAlgebra
import Lax369799Proofs.FiniteCovers
import Mathlib.Order.Preorder.Finite

namespace Lax369799Proofs.FiniteOrderedAlgebra
open Lax369799.RankedSystems (RankedSet)
open Lax369799.FinitePresentations Lax369799.FiniteContextualOrder
open Lax369799.FiniteAcceptance Lax369799.FiniteSyntacticAlgebra

/--
---
conclusion: Lax369799.FiniteOrderedAlgebra.sum_value_meet
---
Choose finite presentation representatives and apply the contextual meet
characterization, using commutation of evaluation with the quotient map.
-/
theorem sum_value_meet {A : RankedSet} (L : Lax369799.Algebras.Language A)
    (E : Algebra (Carrier (Accepting L)))
    (hE : ∀ n (S : FiniteSystem (FiniteSystem A) n),
      E.eval n (relabel (quotientMap (Accepting L)) S) = quotientMap (Accepting L) n (flatten S))
    {n : ℕ} (a b c : Carrier (Accepting L) n) :
    ClassBelow (Accepting L) c (sumValue E a b) ↔
      ClassBelow (Accepting L) c a ∧ ClassBelow (Accepting L) c b := by
  induction a using Quot.inductionOn with
  | h S =>
    induction b using Quot.inductionOn with
    | h T =>
      induction c using Quot.inductionOn with
      | h R =>
        erw [FiniteSyntacticAlgebra.sum_value (Accepting L)
          (FiniteAcceptance.accepting_isomorphic L) E hE S T]
        exact FiniteCovers.sum_meet L R S T

/--
---
conclusion: Lax369799.FiniteOrderedAlgebra.language_recognition
---
Construct the contextual substitution algebra and its recognizing subset.
On reachable deterministic systems, universal yield acceptance is exactly
membership in the unfolding-invariant language.
-/
theorem language_recognition {A : RankedSet} (L : Lax369799.Algebras.Language A)
    (hL : Lax369799.Algebras.UnfoldInvariantLanguage L) :
    ∃ E : Algebra (Carrier (Accepting L)), ∃ P : Set (Carrier (Accepting L) 0),
      ∀ S : Lax369799.RankedSystems.System A 0,
        E.eval 0 (relabel (fun r a => quotientMap (Accepting L) r (atomic a))
          (ofSetSystem S.val)) ∈ P ↔ S ∈ L := by
  obtain ⟨E, hE⟩ := FiniteAcceptance.syntactic_substitution_algebra L
  obtain ⟨P, hP⟩ := FiniteSyntacticAlgebra.contextual_recognition (Accepting L)
    (FiniteAcceptance.accepting_isomorphic L) E hE
  exact ⟨E, P, fun S => (hP (ofSetSystem S.val)).trans (FiniteAcceptance.accepting_system L hL S)⟩

/--
---
conclusion: Lax369799.FiniteOrderedAlgebra.principal_acceptance
---
A nonempty accepting filter in a finite sort has a minimal member.
Closure under meet makes that member least, and upward closure gives
the principal-filter characterization.
-/
theorem principal_acceptance {A : RankedSet} (L : Lax369799.Algebras.Language A)
    (E : Algebra (Carrier (Accepting L)))
    (hE : ∀ n (S : FiniteSystem (FiniteSystem A) n),
      E.eval n (relabel (quotientMap (Accepting L)) S) = quotientMap (Accepting L) n (flatten S))
    (hfinite : Finite (Carrier (Accepting L) 0)) :
    ∃ p, ∀ a, AcceptingClass (Accepting L) a ↔ ClassBelow (Accepting L) p a := by
  classical
  let := hfinite
  have ho := FiniteContextualOrder.class_order (Accepting L) 0
  let : PartialOrder (Carrier (Accepting L) 0) := {
    le := ClassBelow (Accepting L)
    le_refl := ho.1
    le_trans := ho.2.2
    le_antisymm := ho.2.1 }
  have hne : ∃ a, AcceptingClass (Accepting L) a :=
    ⟨quotientMap (Accepting L) 0 (empty A 0), empty A 0, rfl, FiniteAcceptance.accepting_empty L⟩
  let F : Set (Carrier (Accepting L) 0) := AcceptingClass (Accepting L)
  obtain ⟨p, hp, hmin⟩ := (Set.toFinite F).exists_minimal hne
  have ha := FiniteSyntacticAlgebra.accepting_classes (Accepting L)
    (FiniteAcceptance.accepting_isomorphic L)
  refine ⟨p, fun a => ⟨?_, fun h => ha.2 p a hp h⟩⟩
  intro h
  have hm := FiniteSyntacticAlgebra.accepting_sum_value (Accepting L)
    (FiniteAcceptance.accepting_isomorphic L)
    (fun S T hs ht => (FiniteAcceptance.accepting_sum L S T).mpr ⟨hs, ht⟩) E hE p a hp h
  have hl := (sum_value_meet L E hE p a (sumValue E p a)).mp (ho.1 _)
  exact ho.2.2 p (sumValue E p a) a (hmin hm hl.1) hl.2

end Lax369799Proofs.FiniteOrderedAlgebra
