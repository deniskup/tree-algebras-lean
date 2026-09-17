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

axiom contextual_algebra {A : RankedSet} (F : ClosedProperty A) (hF : IsoInvariant F) :
    ∃ E : Algebra (Carrier F), ∀ n (S : FiniteSystem (FiniteSystem A) n),
      E.eval n (relabel (quotientMap F) S) = quotientMap F n (flatten S)

axiom contextual_recognition {A : RankedSet} (F : ClosedProperty A) (hF : IsoInvariant F)
    (E : Algebra (Carrier F))
    (hE : ∀ n (S : FiniteSystem (FiniteSystem A) n),
      E.eval n (relabel (quotientMap F) S) = quotientMap F n (flatten S)) :
    ∃ P : Set (Carrier F 0), ∀ S : FiniteSystem A 0,
      E.eval 0 (relabel (fun r a => quotientMap F r (atomic a)) S) ∈ P ↔ S ∈ F

end Lax369799.FiniteSyntacticAlgebra
