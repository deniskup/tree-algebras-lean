import Lax369799.FiniteAcceptance

/-!
---
title: Planting finite presentations
type: theorem
---
Planting moves initial vertices to roots. Since acceptance checks both
initial and root yields, planting preserves acceptance.
-/
namespace Lax369799.FinitePlant
open RankedSystems (RankedSet)
open FinitePresentations FiniteAcceptance

axiom accepting_plant {A : RankedSet} (L : Algebras.Language A) (S : FiniteSystem A 0) :
    Accepting L (plant S) ↔ Accepting L S

axiom flatten_plant {A : RankedSet} {n : ℕ} (S : FiniteSystem (FiniteSystem A) n) :
    Isomorphic (flatten (plant S)) (plant (flatten S))

axiom accepting_evaluation_plant {A : RankedSet} (L : Algebras.Language A)
    (E : FiniteSyntacticAlgebra.Algebra (FiniteContextualOrder.Carrier (Accepting L)))
    (hE : ∀ n (S : FiniteSystem (FiniteSystem A) n),
      E.eval n (relabel (FiniteContextualOrder.quotientMap (Accepting L)) S) =
        FiniteContextualOrder.quotientMap (Accepting L) n (flatten S))
    (P : FiniteSystem (FiniteContextualOrder.Carrier (Accepting L)) 0) :
    FiniteSyntacticAlgebra.AcceptingClass (Accepting L) (E.eval 0 (plant P)) ↔
      FiniteSyntacticAlgebra.AcceptingClass (Accepting L) (E.eval 0 P)

end Lax369799.FinitePlant
