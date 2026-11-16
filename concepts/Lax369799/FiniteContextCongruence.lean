import Lax369799.FiniteContexts

/-!
---
title: Context tests and simultaneous substitution
type: theorem
---
The set-system clause of Lemma 42. Relations are stated on enumerated
presentations, so compatibility with the manuscript's identification up
to isomorphism is explicit. A reflexive local relation is preserved by
all contexts exactly when it is preserved by simultaneous substitution
into every finite outer shape, for a reflexive transitive target relation.
-/

namespace Lax369799.FiniteContextCongruence
open RankedSystems FinitePresentations FiniteContexts

abbrev RelationFamily (A : RankedSet) := ∀ n, FiniteSystem A n → FiniteSystem A n → Prop

def InContexts {A : RankedSet} (R R' : RelationFamily A) : Prop :=
  ∀ (k n : ℕ) (C : Context A k n) (S T : FiniteSystem A k),
    R k S T → R' n (plug C S) (plug C T)

def InSubstitutions {A : RankedSet} (R R' : RelationFamily A) : Prop :=
  ∀ (B : RankedSet) (n : ℕ) (P : FiniteSystem B n)
    (q r : ∀ v : P.Vertex, FiniteSystem A (P.graph.label v).1),
    (∀ v, R _ (q v) (r v)) → R' n (flatten (withLabels P q)) (flatten (withLabels P r))

axiom context_iff_substitution {A : RankedSet} (R R' : RelationFamily A)
    (hR : ∀ n (S : FiniteSystem A n), R n S S) (hR' : ∀ n (S : FiniteSystem A n), R' n S S)
    (htrans : ∀ n (S T U : FiniteSystem A n), R' n S T → R' n T U → R' n S U)
    (hiso : ∀ n (S T : FiniteSystem A n), Isomorphic S T → R' n S T) :
    InContexts R R' ↔ InSubstitutions R R'

end Lax369799.FiniteContextCongruence
