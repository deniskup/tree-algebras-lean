import Lax369799.FiniteMorphisms

/-!
---
title: Ordered syntactic algebras of finite presentations
type: theorem
---
For yield acceptance, binary disjoint union induces meet on the
contextual quotient. The substitution algebra recognizes the original
language on reachable deterministic systems.
-/

namespace Lax369799.FiniteOrderedAlgebra
open RankedSystems (RankedSet)
open FinitePresentations FiniteContextualOrder FiniteAcceptance FiniteSyntacticAlgebra

axiom sum_value_meet {A : RankedSet} (L : Algebras.Language A)
    (E : Algebra (Carrier (Accepting L)))
    (hE : ∀ n (S : FiniteSystem (FiniteSystem A) n),
      E.eval n (relabel (quotientMap (Accepting L)) S) = quotientMap (Accepting L) n (flatten S))
    {n : ℕ} (a b c : Carrier (Accepting L) n) :
    ClassBelow (Accepting L) c (sumValue E a b) ↔
      ClassBelow (Accepting L) c a ∧ ClassBelow (Accepting L) c b

axiom language_recognition {A : RankedSet} (L : Algebras.Language A)
    (hL : Algebras.UnfoldInvariantLanguage L) :
    ∃ E : Algebra (Carrier (Accepting L)), ∃ P : Set (Carrier (Accepting L) 0),
      ∀ S : RankedSystems.System A 0,
        E.eval 0 (relabel (fun r a => quotientMap (Accepting L) r (atomic a))
          (ofSetSystem S.val)) ∈ P ↔ S ∈ L

end Lax369799.FiniteOrderedAlgebra
