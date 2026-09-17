import Lax369799.Regularization
import Lax369799Proofs.GeneratedAlgebra
import Lax369799Proofs.PolynomialUnfolding

set_option backward.isDefEq.respectTransparency false
namespace Lax369799Proofs.Regularization
open Lax369799.RankedSystems Lax369799.Algebras Lax369799.Morphisms Lax369799.Flattening

/--
---
conclusion: Lax369799.Regularization.generated_closed_invariant
---
Substitute a fixed realizing system for each generated value. Unfold-equivalent
outer systems have unfold-equivalent flattenings over the original alphabet.
Recognition and language invariance transfer membership of the accepting set.
-/
theorem generated_closed_invariant {A B : RankedSet} (E : Algebra B) (η : RankedMap A B)
    (G : Algebra (Lax369799.GeneratedAlgebra.Carrier E η))
    (hG : ∀ n (S : System (Lax369799.GeneratedAlgebra.Carrier E η) n),
      (G.eval n S).val = E.eval n (relabelSystem (Lax369799.GeneratedAlgebra.projection E η) S))
    (F : Set (B 0)) (L : Language A) (hL : UnfoldInvariantLanguage L) (hrec : Recognizes E η F L) :
    Lax369799.PolynomialUnfolding.ClosedInvariant G {b | b.val ∈ F} := by
  intro S T h
  let rep := GeneratedAlgebra.representative E η
  obtain ⟨U, hu⟩ := Flattening.flatten_system (relabelSystem rep S)
  obtain ⟨V, hv⟩ := Flattening.flatten_system (relabelSystem rep T)
  have huv := SystemSubstitution.outer_unfold (relabelSystem rep S) (relabelSystem rep T)
    (SystemSubstitution.relabel_unfold rep h) U V hu hv
  have he : (fun k a => E.eval k (relabelSystem η (rep k a))) = Lax369799.GeneratedAlgebra.projection E η := by
    funext k a
    exact GeneratedAlgebra.representative_value E η k a
  have eu := SystemSubstitution.evaluation E η rep S U hu
  have ev := SystemSubstitution.evaluation E η rep T V hv
  rw [he, ← hG] at eu ev
  change (G.eval 0 S).val ∈ F ↔ (G.eval 0 T).val ∈ F
  rw [← eu, ← ev, ← hrec U, ← hrec V]
  exact hL U V huv

/--
---
conclusion: Lax369799.Regularization.regular_tree_recognizable
---
Restrict the recognizing algebra to its generated values and quotient by
polynomial acceptance equivalence. Both steps preserve recognition and
finite sorts; closed unfolding invariance makes the quotient unfolding-invariant.
-/
theorem regular_tree_recognizable {A : RankedSet} (L : Language A)
    (hL : UnfoldInvariantLanguage L) (hrec : Recognizable L) : RegularTreeRecognizable L := by
  obtain ⟨B, E, η, F, hB, hrec⟩ := hrec
  obtain ⟨G, hG⟩ := GeneratedAlgebra.algebra E η
  let F' : Set (Lax369799.GeneratedAlgebra.Carrier E η 0) := {b | b.val ∈ F}
  obtain ⟨Q, hQ⟩ := PolynomialQuotient.algebra G F'
  refine ⟨_, Q, (fun n a => Lax369799.PolynomialQuotient.classMap G F' n
    (Lax369799.GeneratedAlgebra.letter E η n a)), Lax369799.PolynomialQuotient.Accepting G F',
    PolynomialQuotient.finite_carrier G F' (GeneratedAlgebra.finite_carrier E η hB), ?_, ?_⟩
  · exact PolynomialUnfolding.quotient_unfold_invariant G F'
      (generated_closed_invariant E η G hG F L hL hrec) Q hQ
  · exact PolynomialQuotient.recognition G F' Q hQ (Lax369799.GeneratedAlgebra.letter E η) L
      (GeneratedAlgebra.recognition E η G hG F L hrec)

end Lax369799Proofs.Regularization
