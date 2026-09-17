import Lax369799.FiniteSyntacticAlgebra
import Lax369799.SyntacticOrder

/-!
---
title: Yield acceptance of finite presentations
type: definition
---
Acceptance tests the yields starting at initial or root vertices. For an
ordinary finite presentation this is computed on its reachable restriction.
This final observation does not prune intermediate substitution patterns.
The resulting isomorphism-invariant property has a contextual quotient
algebra for unpruned substitution.
-/

namespace Lax369799.FiniteAcceptance
open RankedSystems (RankedSet)
open FinitePresentations FiniteContextualOrder

def Accepting {A : RankedSet} (L : Algebras.Language A) (S : FiniteSystem A 0) : Prop :=
  SyntacticOrder.Accepting L (RankedSystems.trim S.graph)

axiom accepting_isomorphic {A : RankedSet} (L : Algebras.Language A) :
    IsoInvariant (Accepting L)

axiom syntactic_substitution_algebra {A : RankedSet} (L : Algebras.Language A) :
    ∃ E : FiniteSyntacticAlgebra.Algebra (Carrier (Accepting L)),
      ∀ n (S : FiniteSystem (FiniteSystem A) n),
        E.eval n (relabel (quotientMap (Accepting L)) S) =
          quotientMap (Accepting L) n (flatten S)

end Lax369799.FiniteAcceptance
