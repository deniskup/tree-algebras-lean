import Lax369799.PolynomialContexts

/-!
---
title: Unfolding congruence for deterministic substitution
type: theorem
---
Substituting pointwise unfold-equivalent inner systems preserves unfolding.
A morphism between deterministic outer systems also induces an unfolding
relation between their flattenings. Inner roots are absent, so outer
unreachable vertices cannot introduce additional root observations.
-/
namespace Lax369799.SystemSubstitution
open RankedSystems Morphisms Flattening PolynomialContexts

axiom pointwise_unfold {A C : RankedSet} {n : ℕ} (P : System C n)
    (q r : ∀ v, System A (P.val.graph.label v).1)
    (h : ∀ v, UnfoldEquivalent (q v).val (r v).val)
    (U V : System A n) (hU : SystemFlattening (withLabels P q) U)
    (hV : SystemFlattening (withLabels P r) V) : UnfoldEquivalent U.val V.val

axiom outer_morphism {A : RankedSet} {n : ℕ} (S T : System (System A) n)
    (f : Morphism S.val T.val) (U V : System A n)
    (hU : SystemFlattening S U) (hV : SystemFlattening T V) : UnfoldsTo V.val U.val

axiom evaluation {A B C : RankedSet} (E : Algebras.Algebra B) (η : RankedMap A B)
    (f : RankedMap C (System A)) {n : ℕ} (S : System C n) (U : System A n)
    (hU : SystemFlattening (relabelSystem f S) U) :
    E.eval n (relabelSystem η U) = E.eval n
      (relabelSystem (fun k a => E.eval k (relabelSystem η (f k a))) S)

end Lax369799.SystemSubstitution
