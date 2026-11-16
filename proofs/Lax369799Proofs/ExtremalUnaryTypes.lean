import Lax369799.ExtremalUnaryTypes
import Lax369799Proofs.ParallelReplacement

namespace Lax369799Proofs.ExtremalUnaryTypes
open Lax369799.RankedSystems (RankedSet)
open Lax369799.FinitePresentations Lax369799.FiniteContexts Lax369799.FiniteContextualOrder
open Lax369799.FiniteAcceptance Lax369799.FiniteSyntacticAlgebra Lax369799.ExpandedSyntacticAlgebra
open Lax369799.FiniteExtremal Lax369799.FiniteNormalForms Lax369799.ExtremalUnaryTypes
open Lax369799.ExtremalContexts (Data)

/--
---
conclusion: Lax369799.ExtremalUnaryTypes.replacement
---
Normalize the accepting context, minimize its unary data, and take the
rank-one split witness. Its lower bound and acceptance hold also in rank one.
-/
theorem replacement {A : RankedSet} (L : Lax369799.Algebras.Language A)
    (hL : Lax369799.Algebras.UnfoldInvariantLanguage L) (hrec : Lax369799.Algebras.Recognizable L)
    (E : SyntacticAlgebra L) (C : Context (Carrier (Accepting L)) 1 0)
    (a : Carrier (Accepting L) 1)
    (ha : AcceptingClass (Accepting L) (E.algebra.eval 0 (plug C (atomic a)))) :
    ∃ b, Selected L E b ∧ ClassBelow (Accepting L) b a ∧
      AcceptingClass (Accepting L) (E.algebra.eval 0 (plug C (atomic b))) := by
  let F := Accepting L
  have hF := FiniteAcceptance.accepting_isomorphic L
  have hc := fun n (S T : FiniteSystem (Carrier F) n) f hf =>
    FiniteOuterMorphisms.evaluation_cover L E.algebra E.evaluates (S := S) (T := T) f hf
  have hup := (FiniteSyntacticAlgebra.accepting_classes F hF).2
  let x₀ : Data (Carrier F) 1 := ⟨plantedBoundary C, pieceValue E.algebra C⟩
  have hx₀ : Accepts F E.algebra a x₀ := by
    change AcceptingClass F
      (E.algebra.eval 0 (plug (normalContext (plantedBoundary C) (pieceValue E.algebra C)) (atomic a)))
    rw [FiniteNormalForms.algebraic_decomposition E.algebra hc C a]
    exact (FinitePlant.accepting_evaluation_plant L E.algebra E.evaluates _).mpr ha
  obtain ⟨x, hxx₀, hx, hmin⟩ := FiniteExtremal.extremal_choice F E.algebra
    (BoundedProfileRefinement.finite_carrier_recognizable L hL hrec 1) a x₀ hx₀
  let b := E.algebra.eval 1 (Lax369799.SplitExtremal.delta x.1 x.2 a)
  refine ⟨b, ⟨a, x, ⟨hx, hmin⟩, rfl⟩,
    SplitExtremal.delta_below L E.algebra E.evaluates (by omega) x a ⟨hx, hmin⟩, ?_⟩
  have hb : Accepts F E.algebra b x := hup _ _ hx
    (SplitExtremal.delta_in_context L E.algebra E.evaluates x a)
  have hb₀ : Accepts F E.algebra b x₀ := hup _ _ hb
    (FiniteExtremal.data_monotone L E.algebra E.evaluates x x₀ hxx₀ b)
  change AcceptingClass F
    (E.algebra.eval 0 (plug (normalContext (plantedBoundary C) (pieceValue E.algebra C)) (atomic b))) at hb₀
  rw [FiniteNormalForms.algebraic_decomposition E.algebra hc C b] at hb₀
  exact (FinitePlant.accepting_evaluation_plant L E.algebra E.evaluates _).mp hb₀

/--
---
conclusion: Lax369799.ExtremalUnaryTypes.normal_test
---
Every selected type inherits the exact context-data test of its witness.
-/
theorem normal_test {A : RankedSet} (L : Lax369799.Algebras.Language A) (E : SyntacticAlgebra L)
    (b : Carrier (Accepting L) 1) (hb : Selected L E b) :
    ∃ x : Data (Carrier (Accepting L)) 1, ∀ y,
      Accepts (Accepting L) E.algebra b y ↔ DataBelow (Accepting L) x y := by
  obtain ⟨a, x, hx, rfl⟩ := hb
  exact ⟨x, fun y => SplitExtremal.acceptance_iff_dataBelow L E.algebra E.evaluates (by omega) x y a hx⟩

end Lax369799Proofs.ExtremalUnaryTypes
