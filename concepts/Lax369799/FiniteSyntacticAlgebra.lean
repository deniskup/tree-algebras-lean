import Lax369799.FiniteContextualOrder

/-!
---
title: Contextual quotient algebras of finite presentations
type: theorem
---
The contextual quotient carries evaluation for unpruned finite
presentations. Evaluation respects isomorphism, the atomic unit, and
associativity. This is the substitution-algebra structure alone; no
yield-continuity law is asserted here.
-/

namespace Lax369799.FiniteSyntacticAlgebra
open RankedSystems (RankedSet)
open FinitePresentations FiniteContextualOrder

structure Algebra (A : RankedSet) where
  eval : ∀ n, FiniteSystem A n → A n
  unit : ∀ n (a : A n), eval n (atomic a) = a
  associative : ∀ n (S : FiniteSystem (FiniteSystem A) n),
    eval n (relabel eval S) = eval n (flatten S)
  isomorphic : ∀ n (S T : FiniteSystem A n), Isomorphic S T → eval n S = eval n T

def sumValue {A : RankedSet} (E : Algebra A) {n : ℕ} (a b : A n) : A n :=
  E.eval n (binary a b)

def AcceptingClass {A : RankedSet} (F : ClosedProperty A) (a : Carrier F 0) : Prop :=
  ∃ S : FiniteSystem A 0, quotientMap F 0 S = a ∧ S ∈ F

axiom accepting_classes {A : RankedSet} (F : ClosedProperty A) (hF : IsoInvariant F) :
    (∀ S, AcceptingClass F (quotientMap F 0 S) ↔ S ∈ F) ∧
    (∀ a b, AcceptingClass F a → ClassBelow F a b → AcceptingClass F b)

axiom contextual_algebra {A : RankedSet} (F : ClosedProperty A) (hF : IsoInvariant F) :
    ∃ E : Algebra (Carrier F), ∀ n (S : FiniteSystem (FiniteSystem A) n),
      E.eval n (relabel (quotientMap F) S) = quotientMap F n (flatten S)

axiom contextual_recognition {A : RankedSet} (F : ClosedProperty A) (hF : IsoInvariant F)
    (E : Algebra (Carrier F))
    (hE : ∀ n (S : FiniteSystem (FiniteSystem A) n),
      E.eval n (relabel (quotientMap F) S) = quotientMap F n (flatten S)) :
    ∃ P : Set (Carrier F 0), ∀ S : FiniteSystem A 0,
      E.eval 0 (relabel (fun r a => quotientMap F r (atomic a)) S) ∈ P ↔ S ∈ F

axiom evaluation_monotone {A B : RankedSet} (F : ClosedProperty A) (hF : IsoInvariant F)
    (E : Algebra (Carrier F))
    (hE : ∀ n (S : FiniteSystem (FiniteSystem A) n),
      E.eval n (relabel (quotientMap F) S) = quotientMap F n (flatten S))
    {n : ℕ} (P : FiniteSystem B n)
    (q r : ∀ v : P.Vertex, Carrier F (P.graph.label v).1)
    (h : ∀ v, ClassBelow F (q v) (r v)) :
    ClassBelow F (E.eval n (withLabels P q)) (E.eval n (withLabels P r))

axiom sum_value {A : RankedSet} (F : ClosedProperty A) (hF : IsoInvariant F)
    (E : Algebra (Carrier F))
    (hE : ∀ n (S : FiniteSystem (FiniteSystem A) n),
      E.eval n (relabel (quotientMap F) S) = quotientMap F n (flatten S))
    {n : ℕ} (S T : FiniteSystem A n) :
    sumValue E (quotientMap F n S) (quotientMap F n T) = quotientMap F n (sum S T)

axiom accepting_sum_value {A : RankedSet} (F : ClosedProperty A) (hF : IsoInvariant F)
    (hSum : ∀ S T, S ∈ F → T ∈ F → sum S T ∈ F)
    (E : Algebra (Carrier F))
    (hE : ∀ n (S : FiniteSystem (FiniteSystem A) n),
      E.eval n (relabel (quotientMap F) S) = quotientMap F n (flatten S))
    (a b : Carrier F 0) :
    AcceptingClass F a → AcceptingClass F b → AcceptingClass F (sumValue E a b)

end Lax369799.FiniteSyntacticAlgebra
