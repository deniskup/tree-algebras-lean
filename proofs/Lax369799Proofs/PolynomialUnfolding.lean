import Lax369799.PolynomialUnfolding
import Lax369799Proofs.PolynomialQuotient
import Lax369799Proofs.SystemSubstitution

set_option backward.isDefEq.respectTransparency false
namespace Lax369799Proofs.PolynomialUnfolding
open Lax369799.RankedSystems Lax369799.Algebras Lax369799.Morphisms Lax369799.Flattening
open Lax369799.PolynomialContexts Lax369799.PolynomialUnfolding

/--
---
conclusion: Lax369799.PolynomialUnfolding.realization
---
Realize constants by atomic systems and each evaluation node by flattening
the chosen inner realizations. Associativity gives the values; pointwise
substitution congruence gives the common unfolding class.
-/
theorem realization {B : RankedSet} (E : Algebra B) {k n : ℕ} {p : B k → B n}
    (hp : Polynomial E k n p) (S T : System B k) (h : UnfoldEquivalent S.val T.val) :
    ∃ U V : System B n, E.eval n U = p (E.eval k S) ∧ E.eval n V = p (E.eval k T) ∧
      UnfoldEquivalent U.val V.val := by
  classical
  induction hp with
  | «variable» => exact ⟨S, T, rfl, rfl, h⟩
  | constant n b =>
    exact ⟨atomicSystem b, atomicSystem b, E.unit n b, E.unit n b,
      ⟨_, ⟨MorphismTheorems.identity _, MorphismTheorems.identity_surjective _⟩,
        ⟨MorphismTheorems.identity _, MorphismTheorems.identity_surjective _⟩⟩⟩
  | @evaluation n P f hf ih =>
    choose U V hu hv he using ih
    obtain ⟨X, hx⟩ := Flattening.flatten_system (withLabels P U)
    obtain ⟨Y, hy⟩ := Flattening.flatten_system (withLabels P V)
    refine ⟨X, Y, ?_, ?_, SystemSubstitution.pointwise_unfold P U V he X Y hx hy⟩
    · have hh := E.associative n (withLabels P U) X hx
      change E.eval n (withLabels P (fun v => E.eval _ (U v))) = E.eval n X at hh
      rw [show (fun v => E.eval _ (U v)) = (fun v => f v (E.eval k S)) from funext hu] at hh
      exact hh.symm
    · have hh := E.associative n (withLabels P V) Y hy
      change E.eval n (withLabels P (fun v => E.eval _ (V v))) = E.eval n Y at hh
      rw [show (fun v => E.eval _ (V v)) = (fun v => f v (E.eval k T)) from funext hv] at hh
      exact hh.symm

private def relabelMorphism {A B : RankedSet} (η : RankedMap A B) {n : ℕ}
    {S T : SetSystem A n} (f : Morphism S T) : Morphism (relabel η S) (relabel η T) where
  toFun := f.toFun
  initial := f.initial
  root := f.root
  label := fun v => congrArg (fun a : Symbol A => (⟨a.1, η a.1 a.2⟩ : Symbol B)) (f.label v)
  edge := f.edge

/--
---
conclusion: Lax369799.PolynomialUnfolding.quotient_unfold_invariant
---
Relabel by fixed representatives. Every closed polynomial test has
unfold-equivalent realizing systems, so closed unfolding invariance makes
all tests agree. Their evaluated values are therefore the same quotient class.
-/
theorem quotient_unfold_invariant {B : RankedSet} (E : Algebra B) (F : Set (B 0))
    (hF : ClosedInvariant E F) (Q : Algebra (Lax369799.PolynomialQuotient.Carrier E F))
    (hQ : ∀ n (S : System B n), Q.eval n (relabelSystem (Lax369799.PolynomialQuotient.classMap E F) S) =
      Lax369799.PolynomialQuotient.classMap E F n (E.eval n S)) : UnfoldInvariant Q := by
  classical
  intro n S T h
  let rep : RankedMap (Lax369799.PolynomialQuotient.Carrier E F) B := fun _ a => a.out
  have relabel_rep (S : System (Lax369799.PolynomialQuotient.Carrier E F) n) :
      relabelSystem (Lax369799.PolynomialQuotient.classMap E F) (relabelSystem rep S) = S := by
    have he : (fun k a => Lax369799.PolynomialQuotient.classMap E F k (rep k a)) = (fun _ a => a) := by
      funext k a
      exact Quot.out_eq a
    change relabelSystem (fun k a => Lax369799.PolynomialQuotient.classMap E F k (rep k a)) S = S
    rw [he]
    rfl
  rw [← relabel_rep S, hQ, ← relabel_rep T, hQ]
  apply Quot.sound
  intro p hp
  have he : UnfoldEquivalent (relabelSystem rep S).val (relabelSystem rep T).val := by
    obtain ⟨R, ⟨f, hf⟩, ⟨g, hg⟩⟩ := h
    exact ⟨relabel rep R, ⟨relabelMorphism rep f, hf⟩, ⟨relabelMorphism rep g, hg⟩⟩
  obtain ⟨U, V, hu, hv, huv⟩ := realization E hp (relabelSystem rep S) (relabelSystem rep T) he
  rw [← hu, ← hv]
  exact hF U V huv

end Lax369799Proofs.PolynomialUnfolding
