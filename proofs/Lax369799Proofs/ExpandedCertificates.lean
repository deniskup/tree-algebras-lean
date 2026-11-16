import Lax369799.ExpandedCertificates
import Lax369799Proofs.FiniteVertexReplacement

namespace Lax369799Proofs.ExpandedCertificates
open Lax369799.RankedSystems (RankedSet System trim)
open Lax369799.FinitePresentations Lax369799.FiniteContextualOrder Lax369799.FiniteAcceptance
open Lax369799.FiniteSyntacticAlgebra Lax369799.ExpandedSyntacticAlgebra
open Lax369799.ExpandedContinuity Lax369799.ExpandedCertificates

/--
---
conclusion: Lax369799.ExpandedCertificates.acceptance_iff_certificate
---
Completeness uses simultaneous replacement and expanded continuity.
Soundness uses monotone evaluation and upward closure of acceptance.
-/
theorem acceptance_iff_certificate {A B : RankedSet} (L : Lax369799.Algebras.Language A)
    (hL : Lax369799.Algebras.UnfoldInvariantLanguage L) (hrec : Lax369799.Algebras.Recognizable L)
    (E : SyntacticAlgebra L) (P : FiniteSystem B 0)
    (q : ∀ v : P.Vertex, Carrier (Accepting L) (P.graph.label v).1) :
    AcceptingClass (Accepting L) (E.algebra.eval 0 (withLabels P q)) ↔
      Nonempty (Certificate L E P q) := by
  constructor
  · intro ha
    obtain ⟨r, hr, ha⟩ := FiniteVertexReplacement.simultaneous_replacement L hL hrec E P q ha
    obtain ⟨p, hp⟩ := ExpandedSyntacticAlgebra.representatives_exist L (withLabels P r)
    exact ⟨⟨r, hr, p, hp, (ExpandedContinuity.closed_continuity L E.algebra E.evaluates _ p hp).mp ha⟩⟩
  · rintro ⟨c⟩
    have ha := (ExpandedContinuity.closed_continuity L E.algebra E.evaluates _
      c.representatives c.represents).mpr c.accepts
    have hle := FiniteSyntacticAlgebra.evaluation_monotone (Accepting L)
      (FiniteAcceptance.accepting_isomorphic L) E.algebra E.evaluates P c.labels q
      (fun v => (c.local_choice v).2)
    exact (FiniteSyntacticAlgebra.accepting_classes (Accepting L)
      (FiniteAcceptance.accepting_isomorphic L)).2 _ _ ha hle

/--
---
conclusion: Lax369799.ExpandedCertificates.input_evaluation
---
Quotient evaluation commutes with flattening; the atomic substitution is
the identity up to isomorphism and hence has the same contextual class.
-/
theorem input_evaluation {A : RankedSet} (L : Lax369799.Algebras.Language A)
    (E : SyntacticAlgebra L) {n : ℕ} (S : FiniteSystem A n) :
    E.algebra.eval n (relabel (fun k a => quotientMap (Accepting L) k (atomic a)) S) =
      quotientMap (Accepting L) n S := by
  have h := E.evaluates n (relabel (fun _ a => atomic a) S)
  exact h.trans (Quot.sound (FiniteContextualOrder.contextual_iso (Accepting L)
    (FiniteAcceptance.accepting_isomorphic L) _ _ (UntrimmedFlattening.inner_atomic S)))

/--
---
conclusion: Lax369799.ExpandedCertificates.language_iff_certificate
---
The canonical quotient labels evaluate to the input class. Recognition
then turns the certificate characterization into language membership.
-/
theorem language_iff_certificate {A : RankedSet} (L : Lax369799.Algebras.Language A)
    (hL : Lax369799.Algebras.UnfoldInvariantLanguage L) (hrec : Lax369799.Algebras.Recognizable L)
    (E : SyntacticAlgebra L) (S : System A 0) :
    S ∈ L ↔ Nonempty (Certificate L E (ofSetSystem S.val)
      (fun v => quotientMap (Accepting L) _ (atomic (S.val.graph.label v).2))) := by
  have h := acceptance_iff_certificate L hL hrec E (ofSetSystem S.val)
    (fun v => quotientMap (Accepting L) _ (atomic (S.val.graph.label v).2))
  change AcceptingClass (Accepting L) (E.algebra.eval 0
    (relabel (fun k a => quotientMap (Accepting L) k (atomic a)) (ofSetSystem S.val))) ↔ _ at h
  rw [input_evaluation L E] at h
  exact (ExpandedSyntacticAlgebra.recognition L hL S).symm.trans h

end Lax369799Proofs.ExpandedCertificates
