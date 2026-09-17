import Lax369799.FiniteContexts
import Lax369799.FiniteOrderedAlgebra
import Lax369799.ContextDecomposition

/-!
---
title: Context decomposition without pruning
type: theorem
---
Retain all vertices in the unary pieces and in their recomposition. The
projection covers every original vertex, including unreachable vertices,
and restores the hole's initial flag, root flag, and self-loops.
-/
namespace Lax369799.FiniteDecomposition
open RankedSystems (RankedSet Presentation)
open Flattening (WithHole IsHole)
open FinitePresentations FiniteContexts
open ContextDecomposition (Boundary CopyVertex recomposePresentation)

noncomputable def holeVertex {A : RankedSet} {k : ℕ} (C : Context A k 0) :
    C.system.Vertex := Classical.choose C.one_hole

abbrev BodyVertex {A : RankedSet} {k : ℕ} (C : Context A k 0) :=
  {v : C.system.Vertex // v ≠ holeVertex C}

noncomputable def boundary {A : RankedSet} {k : ℕ} (C : Context A k 0) : Boundary k where
  initial := holeVertex C ∈ C.system.graph.initial
  root := holeVertex C ∈ C.system.graph.root
  loops := {d | C.system.graph.edge (holeVertex C) d.val (.inl (holeVertex C))}

noncomputable def piece {A : RankedSet} {k : ℕ} (C : Context A k 0)
    (i : Fin (k + 1)) : Presentation (WithHole A k) 1 (BodyVertex C) where
  label := fun v => C.system.graph.label v.val
  initial := fun v => (i = 0 ∧ v.val ∈ C.system.graph.initial) ∨
    ∃ d : Fin k, i = d.succ ∧ C.system.graph.edge (holeVertex C) d.val (.inl v.val)
  root := fun v => v.val ∈ C.system.graph.root
  edge := fun v d t => match t with
    | .inl w => C.system.graph.edge v.val d (.inl w.val)
    | .inr _ => C.system.graph.edge v.val d (.inl (holeVertex C))
  direction_valid := by
    intro v d t ht
    cases t with
    | inl w => exact C.system.graph.direction_valid v.val d _ ht
    | inr i => exact C.system.graph.direction_valid v.val d _ ht

noncomputable def recompose {A : RankedSet} {k : ℕ} (C : Context A k 0) :
    FiniteSystem (WithHole A k) 0 := by
  classical
  exact enumerate (recomposePresentation (boundary C) (piece C))

axiom piece_has_no_hole {A : RankedSet} {k : ℕ} (C : Context A k 0)
    (i : Fin (k + 1)) (v : BodyVertex C) : ¬ IsHole ((piece C i).label v)

axiom decomposition_cover {A : RankedSet} {k : ℕ} (C : Context A k 0) :
    ∃ f : PresentationCovers.Cover (recompose C).graph C.system.graph, Function.Surjective f.toFun

axiom recompose_one_hole {A : RankedSet} {k : ℕ} (C : Context A k 0) :
    ∃! v, IsHole ((recompose C).graph.label v)

axiom decomposition_evaluation {A : RankedSet} (L : Algebras.Language A)
    (E : FiniteSyntacticAlgebra.Algebra (FiniteContextualOrder.Carrier (FiniteAcceptance.Accepting L)))
    (hE : ∀ n (S : FiniteSystem (FiniteSystem A) n),
      E.eval n (relabel (FiniteContextualOrder.quotientMap (FiniteAcceptance.Accepting L)) S) =
        FiniteContextualOrder.quotientMap (FiniteAcceptance.Accepting L) n (flatten S))
    {k : ℕ} (C : Context (FiniteContextualOrder.Carrier (FiniteAcceptance.Accepting L)) k 0) :
    ∃ D : Context (FiniteContextualOrder.Carrier (FiniteAcceptance.Accepting L)) k 0,
      D.system = recompose C ∧ ∀ a,
        E.eval 0 (plug D (atomic a)) = E.eval 0 (plug C (atomic a))

end Lax369799.FiniteDecomposition
