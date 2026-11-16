import Lax369799.ParallelReplacement
import Lax369799Proofs.SplitExtremal
import Lax369799Proofs.ExpandedSyntacticAlgebra

namespace Lax369799Proofs.ParallelReplacement
open Lax369799.RankedSystems (RankedSet)
open Lax369799.FinitePresentations Lax369799.FiniteContexts Lax369799.FiniteContextualOrder
open Lax369799.FiniteAcceptance Lax369799.FiniteSyntacticAlgebra Lax369799.ExpandedSyntacticAlgebra
open Lax369799.FiniteExtremal Lax369799.FiniteNormalForms
open Lax369799.ExtremalContexts (Data)

/--
---
conclusion: Lax369799.ParallelReplacement.accepting_parallel
---
Choose an extremal context, then give each successor component its own
rooted incoming piece. The split comparisons give the lower bound;
merging the copies preserves acceptance from the original witness.
-/
theorem accepting_parallel {A : RankedSet} (L : Lax369799.Algebras.Language A)
    (hL : Lax369799.Algebras.UnfoldInvariantLanguage L) (hrec : Lax369799.Algebras.Recognizable L)
    (E : SyntacticAlgebra L) {k : ℕ} (hk : 1 ≤ k)
    (C : Context (Carrier (Accepting L)) k 0) (a : Carrier (Accepting L) k)
    (ha : AcceptingClass (Accepting L) (E.algebra.eval 0 (plug C (atomic a)))) :
    ∃ b : Fin k → Carrier (Accepting L) 1,
      ClassBelow (Accepting L) (E.algebra.eval k (ofSetSystem (Lax369799.DeterministicElements.parallel b))) a ∧
      AcceptingClass (Accepting L) (E.algebra.eval 0 (plug C
        (atomic (E.algebra.eval k (ofSetSystem (Lax369799.DeterministicElements.parallel b)))))) := by
  let F := Accepting L
  have hF := FiniteAcceptance.accepting_isomorphic L
  have hc := fun n (S T : FiniteSystem (Carrier F) n) f hf =>
    FiniteOuterMorphisms.evaluation_cover L E.algebra E.evaluates (S := S) (T := T) f hf
  have hup := (FiniteSyntacticAlgebra.accepting_classes F hF).2
  let x₀ : Data (Carrier F) k := ⟨plantedBoundary C, pieceValue E.algebra C⟩
  have hx₀ : Accepts F E.algebra a x₀ := by
    change AcceptingClass F
      (E.algebra.eval 0 (plug (normalContext (plantedBoundary C) (pieceValue E.algebra C)) (atomic a)))
    rw [FiniteNormalForms.algebraic_decomposition E.algebra hc C a]
    exact (FinitePlant.accepting_evaluation_plant L E.algebra E.evaluates _).mpr ha
  obtain ⟨x, hxx₀, hx, hmin⟩ := FiniteExtremal.extremal_choice F E.algebra
    (BoundedProfileRefinement.finite_carrier_recognizable L hL hrec 1) a x₀ hx₀
  let b := fun i => E.algebra.eval 1 (Lax369799.SplitExtremal.component x.1 x.2 a i)
  refine ⟨b, ?_⟩
  rw [SplitExtremal.parallel_value]
  refine ⟨SplitExtremal.delta_below L E.algebra E.evaluates hk x a ⟨hx, hmin⟩, ?_⟩
  let δ := E.algebra.eval k (Lax369799.SplitExtremal.delta x.1 x.2 a)
  have hδ : Accepts F E.algebra δ x := hup _ _ hx
    (SplitExtremal.delta_in_context L E.algebra E.evaluates x a)
  have hδ₀ : Accepts F E.algebra δ x₀ := hup _ _ hδ
    (FiniteExtremal.data_monotone L E.algebra E.evaluates x x₀ hxx₀ δ)
  change AcceptingClass F
    (E.algebra.eval 0 (plug (normalContext (plantedBoundary C) (pieceValue E.algebra C)) (atomic δ))) at hδ₀
  rw [FiniteNormalForms.algebraic_decomposition E.algebra hc C δ] at hδ₀
  exact (FinitePlant.accepting_evaluation_plant L E.algebra E.evaluates _).mp hδ₀

end Lax369799Proofs.ParallelReplacement
