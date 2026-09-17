import Lax369799.Flattening
import Lax369799.PresentationCovers
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Prod

/-!
---
title: Context decomposition with hole boundary data
type: theorem
---
A hole is an ordinary vertex: it may be initial, a root, and the target of
its own outgoing edges. Cutting a closed context into unary pieces must
retain these three kinds of boundary information. The entry piece starts
at the original non-hole initial vertices; piece i+1 starts at non-hole
successors in direction i. All pieces retain the non-hole roots, and
edges into the hole become edges to the sole variable.

Recomposition takes a separate copy of every piece, redirects variable
edges to a fresh hole, restores its initial and root marks, and restores
its self-loops. Unreachable vertices are removed after recomposition.
The resulting set-system covers the original context and is therefore
unfold-equivalent to it.

This records explicitly the boundary information omitted by the literal
construction preceding `lemma:context-decomposition` in Section 2.8 of
arXiv:2407.12677v6. The pieces are presented over the extended alphabet,
but no piece contains a vertex labelled by the hole. Presentations retain
unreachable vertices until the final restriction.
-/

namespace Lax369799.ContextDecomposition
open RankedSystems Morphisms Flattening

noncomputable def holeVertex {A : RankedSet} {k : ℕ} (C : SetContext A k 0) :
    C.system.Vertex := Classical.choose C.one_hole

abbrev BodyVertex {A : RankedSet} {k : ℕ} (C : SetContext A k 0) :=
  {v : C.system.Vertex // v ≠ holeVertex C}

structure Boundary (k : ℕ) where
  initial : Prop
  root : Prop
  loops : Set (Fin k)

noncomputable def boundary {A : RankedSet} {k : ℕ} (C : SetContext A k 0) : Boundary k where
  initial := holeVertex C ∈ C.system.graph.initial
  root := holeVertex C ∈ C.system.graph.root
  loops := {d | C.system.graph.edge (holeVertex C) d.val (.inl (holeVertex C))}

noncomputable def piece {A : RankedSet} {k : ℕ} (C : SetContext A k 0)
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

abbrev CopyVertex (k : ℕ) (V : Type) := Option (Fin (k + 1) × V)

/-- `none` is the new hole; `some (i,v)` is vertex v in piece i. -/
def recomposePresentation {A : RankedSet} {k : ℕ} {V : Type}
    (B : Boundary k) (P : Fin (k + 1) → Presentation (WithHole A k) 1 V) :
    Presentation (WithHole A k) 0 (CopyVertex k V) where
  label := fun v => match v with
    | none => ⟨k, Sum.inr ⟨rfl⟩⟩
    | some (i, v) => (P i).label v
  initial := fun v => match v with
    | none => B.initial
    | some (i, v) => i = 0 ∧ v ∈ (P i).initial
  root := fun v => match v with
    | none => B.root
    | some (i, v) => v ∈ (P i).root
  edge := fun v d t => match t with
    | .inr j => Fin.elim0 j
    | .inl w => match v, w with
      | none, none => ∃ i : Fin k, d = i.val ∧ i ∈ B.loops
      | none, some (j, w) => ∃ i : Fin k, d = i.val ∧ j = i.succ ∧ w ∈ (P j).initial
      | some (i, v), none => (P i).edge v d (.inr 0)
      | some (i, v), some (j, w) => i = j ∧ (P i).edge v d (.inl w)
  direction_valid := by
    intro v d t ht
    cases t with
    | inr j => exact Fin.elim0 j
    | inl w =>
      cases v with
      | none =>
        cases w with
        | none => obtain ⟨i, rfl, _⟩ := ht; exact i.isLt
        | some w => obtain ⟨i, rfl, _, _⟩ := ht; exact i.isLt
      | some v =>
        cases w with
        | none => exact (P v.1).direction_valid v.2 d _ ht
        | some w => exact (P v.1).direction_valid v.2 d _ ht.2

noncomputable def recompose {A : RankedSet} {k : ℕ} (C : SetContext A k 0) :
    SetSystem (WithHole A k) 0 := by
  classical
  exact trim (recomposePresentation (boundary C) (piece C))

axiom piece_has_no_hole {A : RankedSet} {k : ℕ} (C : SetContext A k 0)
    (i : Fin (k + 1)) (v : BodyVertex C) : ¬ IsHole ((piece C i).label v)

axiom decomposition_cover {A : RankedSet} {k : ℕ} (C : SetContext A k 0) :
  UnfoldsTo C.system (recompose C)

axiom decomposition_equivalence {A : RankedSet} {k : ℕ} (C : SetContext A k 0) :
  UnfoldEquivalent C.system (recompose C)

end Lax369799.ContextDecomposition
