import Lax369799.FiniteDecomposition
import Lax369799.ExtremalContexts

/-!
---
title: Unary normal forms without pruning
type: theorem
---
Evaluate the unpruned unary pieces of a context. Together with the hole's
planted root flag and loop directions, these values describe a normal
context whose evaluation is the planted evaluation of the original.
-/
namespace Lax369799.FiniteNormalForms
open RankedSystems (RankedSet Presentation)
open Flattening (WithHole IsHole)
open FinitePresentations FiniteContexts FiniteDecomposition FiniteSyntacticAlgebra

/-- The label of a non-hole vertex is an ordinary letter of the same rank. -/
noncomputable def ordinaryLetter {A : RankedSet} {k : ℕ} (C : Context A k 0)
    (v : BodyVertex C) :
    {a : A (C.system.graph.label v.val).1 // (C.system.graph.label v.val).2 = Sum.inl a} := by
  cases h : (C.system.graph.label v.val).2 with
  | inl a => exact ⟨a, rfl⟩
  | inr hkr =>
    have hv : IsHole (C.system.graph.label v.val) := ⟨hkr, h⟩
    exact False.elim (v.property ((Classical.choose_spec C.one_hole).2 v.val hv))

noncomputable def ordinaryPiece {A : RankedSet} {k : ℕ} (C : Context A k 0)
    (i : Fin (k + 1)) : Presentation A 1 (BodyVertex C) where
  label := fun v => ⟨(C.system.graph.label v.val).1, (ordinaryLetter C v).val⟩
  initial := (piece C i).initial
  root := (piece C i).root
  edge := (piece C i).edge
  direction_valid := (piece C i).direction_valid

noncomputable def pieceValue {A : RankedSet} (E : Algebra A) {k : ℕ}
    (C : Context A k 0) (i : Fin (k + 1)) : A 1 := by
  classical
  exact E.eval 1 (enumerate (ordinaryPiece C i))

noncomputable def plantedBoundary {A : RankedSet} {k : ℕ} (C : Context A k 0) :
    ExtremalContexts.Boundary k where
  root := (boundary C).initial ∨ (boundary C).root
  loops := (boundary C).loops

def normalContext {A : RankedSet} {k : ℕ} (B : ExtremalContexts.Boundary k)
    (m : Fin (k + 1) → A 1) : Context A k 0 :=
  ⟨ofSetSystem (ExtremalContexts.normalContext B m).system,
    (ExtremalContexts.normalContext B m).one_hole⟩

axiom algebraic_decomposition {A : RankedSet} (E : Algebra A)
    (hcover : ∀ n (S T : FiniteSystem A n) (f : PresentationCovers.Cover S.graph T.graph),
      Function.Surjective f.toFun → E.eval n S = E.eval n T)
    {k : ℕ} (C : Context A k 0) (a : A k) :
    E.eval 0 (plug (normalContext (plantedBoundary C) (pieceValue E C)) (atomic a)) =
      E.eval 0 (plant (plug C (atomic a)))

end Lax369799.FiniteNormalForms
