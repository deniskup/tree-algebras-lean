import Lax369799.FiniteVertexReplacement

/-!
---
title: Acceptance certificates retaining expanded resolutions
type: theorem
---
A certificate chooses a deterministic value below each vertex label and
representatives for the chosen values. It requires acceptance of all yields
of the expanded presentation. This is a characterization of acceptance,
not yet a finite-state branch condition.
-/
namespace Lax369799.ExpandedCertificates
open RankedSystems (RankedSet System trim)
open FinitePresentations FiniteContextualOrder FiniteAcceptance FiniteSyntacticAlgebra
open ExpandedSyntacticAlgebra ExpandedContinuity

structure Certificate {A B : RankedSet} (L : Algebras.Language A)
    (E : SyntacticAlgebra L) (P : FiniteSystem B 0)
    (q : ∀ v : P.Vertex, Carrier (Accepting L) (P.graph.label v).1) where
  labels : ∀ v : P.Vertex, Carrier (Accepting L) (P.graph.label v).1
  local_choice : ∀ v, FiniteExtremal.Deterministic E.algebra (labels v) ∧
    ClassBelow (Accepting L) (labels v) (q v)
  representatives : Representatives L (withLabels P labels)
  represents : Represents L (withLabels P labels) representatives
  accepts : ∀ T, Morphisms.Yield (trim (expansion L (withLabels P labels) representatives).graph) T →
    Admissible L T

axiom acceptance_iff_certificate {A B : RankedSet} (L : Algebras.Language A)
    (hL : Algebras.UnfoldInvariantLanguage L) (hrec : Algebras.Recognizable L)
    (E : SyntacticAlgebra L) (P : FiniteSystem B 0)
    (q : ∀ v : P.Vertex, Carrier (Accepting L) (P.graph.label v).1) :
    AcceptingClass (Accepting L) (E.algebra.eval 0 (withLabels P q)) ↔
      Nonempty (Certificate L E P q)

axiom input_evaluation {A : RankedSet} (L : Algebras.Language A)
    (E : SyntacticAlgebra L) {n : ℕ} (S : FiniteSystem A n) :
    E.algebra.eval n (relabel (fun k a => quotientMap (Accepting L) k (atomic a)) S) =
      quotientMap (Accepting L) n S

axiom language_iff_certificate {A : RankedSet} (L : Algebras.Language A)
    (hL : Algebras.UnfoldInvariantLanguage L) (hrec : Algebras.Recognizable L)
    (E : SyntacticAlgebra L) (S : System A 0) :
    S ∈ L ↔ Nonempty (Certificate L E (ofSetSystem S.val)
      (fun v => quotientMap (Accepting L) _ (atomic (S.val.graph.label v).2)))

end Lax369799.ExpandedCertificates
