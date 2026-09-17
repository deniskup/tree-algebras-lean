import Lax369799.FiniteOrderedAlgebra
import Lax369799Proofs.FiniteCovers

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

end Lax369799Proofs.FiniteOrderedAlgebra
