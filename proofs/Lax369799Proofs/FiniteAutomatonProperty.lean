import Lax369799.FiniteAutomatonProperty
import Lax369799Proofs.FiniteDeltaComparison

namespace Lax369799Proofs.FiniteAutomatonProperty
open Lax369799.RankedSystems (RankedSet)
open Lax369799.FinitePresentations Lax369799.FiniteContexts Lax369799.FiniteContextualOrder
open Lax369799.FiniteSyntacticAlgebra Lax369799.FiniteAcceptance Lax369799.FiniteExtremal
open Lax369799.FiniteNormalForms
open Lax369799.ExtremalContexts (Data)

/--
---
conclusion: Lax369799.FiniteAutomatonProperty.automaton_property
---
Normalize and plant the accepting context, then minimize its boundary and
unary data. Delta is deterministic, below the original value, and accepted
in the extremal normal context. Monotonicity, the normal-form equation,
and planting invariance return acceptance to the original context.
-/
theorem automaton_property {A : RankedSet} (L : Lax369799.Algebras.Language A)
    (E : Algebra (Carrier (Accepting L)))
    (hE : ∀ n (S : FiniteSystem (FiniteSystem A) n),
      E.eval n (relabel (quotientMap (Accepting L)) S) = quotientMap (Accepting L) n (flatten S))
    (hfinite : Finite (Carrier (Accepting L) 1))
    {k : ℕ} (C : Context (Carrier (Accepting L)) k 0) (a : Carrier (Accepting L) k)
    (ha : AcceptingClass (Accepting L) (E.eval 0 (plug C (atomic a)))) :
    ∃ δ, Deterministic E δ ∧ ClassBelow (Accepting L) δ a ∧
      AcceptingClass (Accepting L) (E.eval 0 (plug C (atomic δ))) := by
  let F := Accepting L
  have hF := FiniteAcceptance.accepting_isomorphic L
  have hc := fun n (S T : FiniteSystem (Carrier F) n) f hf =>
    FiniteOuterMorphisms.evaluation_cover L E hE (S := S) (T := T) f hf
  have hup := (FiniteSyntacticAlgebra.accepting_classes F hF).2
  by_cases hk : k ≤ 1
  · exact ⟨a, ⟨atomic a, fun _ => hk, E.unit k a⟩,
      (FiniteContextualOrder.class_order F k).1 a, ha⟩
  · have hk : 2 ≤ k := by omega
    let x₀ : Data (Carrier F) k := ⟨plantedBoundary C, pieceValue E C⟩
    have hx₀ : Accepts F E a x₀ := by
      change AcceptingClass F
        (E.eval 0 (plug (normalContext (plantedBoundary C) (pieceValue E C)) (atomic a)))
      rw [FiniteNormalForms.algebraic_decomposition E hc C a]
      exact (FinitePlant.accepting_evaluation_plant L E hE _).mpr ha
    obtain ⟨x, hxx₀, hx, hmin⟩ := FiniteExtremal.extremal_choice F E hfinite a x₀ hx₀
    let δ := E.eval k (delta x.1 x.2 a)
    refine ⟨δ, FiniteExtremal.delta_deterministic E x.1 x.2 a,
      FiniteDeltaComparison.delta_below L E hE hk x a ⟨hx, hmin⟩, ?_⟩
    have hδ : Accepts F E δ x := hup _ _ hx (FiniteDeltaContext.delta_in_context L E hE x a)
    have hδ₀ : Accepts F E δ x₀ := hup _ _ hδ (FiniteExtremal.data_monotone L E hE x x₀ hxx₀ δ)
    change AcceptingClass F
      (E.eval 0 (plug (normalContext (plantedBoundary C) (pieceValue E C)) (atomic δ))) at hδ₀
    rw [FiniteNormalForms.algebraic_decomposition E hc C δ] at hδ₀
    exact (FinitePlant.accepting_evaluation_plant L E hE _).mp hδ₀

end Lax369799Proofs.FiniteAutomatonProperty
