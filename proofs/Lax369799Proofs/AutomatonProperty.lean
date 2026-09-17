import Lax369799.AutomatonPropertyTheorem
import Lax369799Proofs.ExtremalContexts
import Lax369799Proofs.NormalMonotonicity
import Lax369799Proofs.DeltaComparison

namespace Lax369799Proofs.AutomatonProperty
open Lax369799.RankedSystems Lax369799.Flattening Lax369799.SetAlgebras
open Lax369799.AutomatonProperty Lax369799.ExtremalContexts
open Lax369799.AlgebraicDecomposition

/--
---
conclusion: Lax369799.AutomatonPropertyTheorem.automaton_property
---
Normalize the planted context, then minimize both its boundary data and
unary values. The deterministic Delta witness is below the original
letter and remains accepting. Monotonicity and the algebraic normal form
transfer acceptance back to the original context.
-/
theorem automaton_property {A : RankedSet} (E : SetAlgebra A)
    (hA : RankwiseFinite A) (f : A 0)
    (hp : PlantInvariant E f) (hs : OrderSeparating E f) : HasAutomatonProperty E f := by
  intro k C a hCa
  by_cases hk : k ≤ 1
  · exact ⟨a, SetAlgebraTheorems.low_rank_deterministic E hk a,
      (SetAlgebraTheorems.order_laws E k).1 a, hCa⟩
  · have hk : 2 ≤ k := by omega
    let x₀ : Data A k := ⟨plantedBoundary C, pieceValue E C⟩
    have hx₀ : Accepts E f a x₀ := by
      change Below E f (E.eval 0 (plug (normalContext (plantedBoundary C) (pieceValue E C)) (atomic a)))
      rw [AlgebraicDecomposition.algebraic_decomposition E C a]
      exact (hp (plug C (atomic a))).mp hCa
    obtain ⟨x, hxx₀, hx, hmin⟩ := ExtremalContexts.extremal_choice E hA f a x₀ hx₀
    let δ := E.eval k (delta x.1 x.2 a)
    refine ⟨δ, ExtremalContexts.delta_deterministic E x.1 x.2 a,
      DeltaComparison.delta_below E f hp hs hk x a ⟨hx, hmin⟩, ?_⟩
    have hδ : Accepts E f δ x := (SetAlgebraTheorems.order_laws E 0).2.2.1 _ _ _ hx
      (DeltaContext.delta_in_context E x a)
    have hδ₀ : Accepts E f δ x₀ := (SetAlgebraTheorems.order_laws E 0).2.2.1 _ _ _ hδ
      (NormalMonotonicity.data_monotone E x x₀ hxx₀ δ)
    change Below E f (E.eval 0 (plug (normalContext (plantedBoundary C) (pieceValue E C)) (atomic δ))) at hδ₀
    rw [AlgebraicDecomposition.algebraic_decomposition E C δ] at hδ₀
    exact (hp (plug C (atomic δ))).mpr hδ₀

end Lax369799Proofs.AutomatonProperty
