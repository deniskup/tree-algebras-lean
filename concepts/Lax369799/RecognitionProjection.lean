import Lax369799.NonemptyPowersets

/-!
---
title: Existential projection of recognizable languages
type: theorem
---
Forgetting vertex marks preserves recognizability. More generally, a
surjective rank-preserving letter map induces an existential projection:
a system is accepted if its vertices admit labels above their old labels
that form an accepted system. Nonempty powerset evaluation records all
possible evaluations of these choices.
-/
namespace Lax369799.RecognitionProjection
open RankedSystems Algebras PolynomialContexts

def Projected {A B : RankedSet} (η : RankedMap A B) (L : Language A) : Language B :=
  {S | ∃ q : ∀ v, A (S.val.graph.label v).1,
    (∀ v, η _ (q v) = (S.val.graph.label v).2) ∧ withLabels S q ∈ L}

axiom recognizable {A B : RankedSet} (η : RankedMap A B)
    (hη : ∀ n, Function.Surjective (η n)) (L : Language A) (hL : Recognizable L) :
    Recognizable (Projected η L)

end Lax369799.RecognitionProjection
