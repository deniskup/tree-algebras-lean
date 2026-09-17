import Lax369799.GeneratedAlgebra
import Lax369799.PolynomialUnfolding

/-!
---
title: Regular-tree recognition from unfold-invariant recognition
type: theorem
---
An unfold-invariant language recognized by a rankwise-finite algebra has
a rankwise-finite unfolding-invariant recognizing algebra. First restrict
to values realized by systems over the original alphabet. Then quotient by
all closed polynomial acceptance tests.
-/
namespace Lax369799.Regularization
open RankedSystems Algebras

axiom generated_closed_invariant {A B : RankedSet} (E : Algebra B) (η : RankedMap A B)
    (G : Algebra (GeneratedAlgebra.Carrier E η))
    (hG : ∀ n (S : System (GeneratedAlgebra.Carrier E η) n),
      (G.eval n S).val = E.eval n (relabelSystem (GeneratedAlgebra.projection E η) S))
    (F : Set (B 0)) (L : Language A) (hL : UnfoldInvariantLanguage L) (hrec : Recognizes E η F L) :
    PolynomialUnfolding.ClosedInvariant G {b | b.val ∈ F}

axiom regular_tree_recognizable {A : RankedSet} (L : Language A)
    (hL : UnfoldInvariantLanguage L) (hrec : Recognizable L) : RegularTreeRecognizable L

end Lax369799.Regularization
