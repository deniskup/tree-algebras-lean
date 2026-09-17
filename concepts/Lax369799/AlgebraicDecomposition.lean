import Lax369799.ContextDecomposition
import Lax369799.ExtremalContexts

/-!
---
title: Algebraic decomposition with boundary data
type: theorem
---
Remove the hole symbol from each unary piece and evaluate its reachable
part. The resulting unary values, together with the planted hole mark
and its self-loop directions, give the planted normal context used in
the extremal construction. Its evaluation agrees with the planted
original context for every atomic argument.
-/

namespace Lax369799.AlgebraicDecomposition
open RankedSystems Flattening SetAlgebras ContextDecomposition

/-- The label of a non-hole vertex is an ordinary letter of the same rank. -/
noncomputable def ordinaryLetter {A : RankedSet} {k : ℕ} (C : SetContext A k 0)
    (v : BodyVertex C) :
    {a : A (C.system.graph.label v.val).1 // (C.system.graph.label v.val).2 = Sum.inl a} := by
  cases h : (C.system.graph.label v.val).2 with
  | inl a => exact ⟨a, rfl⟩
  | inr hkr =>
    have hv : IsHole (C.system.graph.label v.val) := ⟨hkr, h⟩
    exact False.elim (v.property ((Classical.choose_spec C.one_hole).2 v.val hv))

noncomputable def ordinaryPiece {A : RankedSet} {k : ℕ} (C : SetContext A k 0)
    (i : Fin (k + 1)) : Presentation A 1 (BodyVertex C) where
  label := fun v => ⟨(C.system.graph.label v.val).1, (ordinaryLetter C v).val⟩
  initial := (piece C i).initial
  root := (piece C i).root
  edge := (piece C i).edge
  direction_valid := (piece C i).direction_valid

noncomputable def pieceValue {A : RankedSet} (E : SetAlgebra A) {k : ℕ}
    (C : SetContext A k 0) (i : Fin (k + 1)) : A 1 := by
  classical
  exact E.eval 1 (trim (ordinaryPiece C i))

noncomputable def plantedBoundary {A : RankedSet} {k : ℕ} (C : SetContext A k 0) :
    ExtremalContexts.Boundary k where
  root := (boundary C).initial ∨ (boundary C).root
  loops := (boundary C).loops

axiom algebraic_decomposition {A : RankedSet} (E : SetAlgebra A) {k : ℕ}
    (C : SetContext A k 0) (a : A k) :
    E.eval 0 (plug (ExtremalContexts.normalContext (plantedBoundary C) (pieceValue E C)) (atomic a)) =
      E.eval 0 (plant (plug C (atomic a)))

end Lax369799.AlgebraicDecomposition
