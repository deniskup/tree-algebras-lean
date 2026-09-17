import Lax369799.PolynomialQuotient
import Lax369799.SystemSubstitution

/-!
---
title: Unfolding through polynomial contexts
type: theorem
---
A polynomial applied to a system value can be realized by an actual system.
For unfold-equivalent inputs, choose unfold-equivalent realizations. Thus
closed acceptance invariance under unfolding makes the polynomial quotient
an unfolding-invariant algebra in every rank.
-/
namespace Lax369799.PolynomialUnfolding
open RankedSystems Algebras Morphisms PolynomialContexts

def ClosedInvariant {B : RankedSet} (E : Algebra B) (F : Set (B 0)) : Prop :=
  ∀ S T : System B 0, UnfoldEquivalent S.val T.val → (E.eval 0 S ∈ F ↔ E.eval 0 T ∈ F)

axiom realization {B : RankedSet} (E : Algebra B) {k n : ℕ} {p : B k → B n}
    (hp : Polynomial E k n p) (S T : System B k) (h : UnfoldEquivalent S.val T.val) :
    ∃ U V : System B n, E.eval n U = p (E.eval k S) ∧ E.eval n V = p (E.eval k T) ∧
      UnfoldEquivalent U.val V.val

axiom quotient_unfold_invariant {B : RankedSet} (E : Algebra B) (F : Set (B 0))
    (hF : ClosedInvariant E F) (Q : Algebra (PolynomialQuotient.Carrier E F))
    (hQ : ∀ n (S : System B n), Q.eval n (relabelSystem (PolynomialQuotient.classMap E F) S) =
      PolynomialQuotient.classMap E F n (E.eval n S)) : UnfoldInvariant Q

end Lax369799.PolynomialUnfolding
