import Lax369799.Morphisms
import Lax369799.Flattening

/- A check of the nullary-hole boundary case in Section 2.8 of v6.
   This file is a local audit, not an Archive concept or proof. -/
namespace ContextDecompositionAudit
open Lax369799.RankedSystems Lax369799.Morphisms Lax369799.Flattening

def empty (A : RankedSet) (n : ℕ) : SetSystem A n where
  size := 0
  graph := {
    label := Fin.elim0
    initial := ∅
    root := ∅
    edge := fun _ _ _ => False
    direction_valid := fun v => Fin.elim0 v }
  reachable := fun v => Fin.elim0 v

def alphabet : RankedSet := fun _ => Empty

def hole : WithHole alphabet 0 0 := Sum.inr ⟨rfl⟩

def C : SetContext alphabet 0 0 where
  system := atomic hole
  one_hole := by
    refine ⟨(⟨0, Nat.zero_lt_one⟩ : Fin 1), ⟨⟨rfl⟩, rfl⟩, ?_⟩
    intro v _
    exact Subsingleton.elim (α := Fin 1) v _

-- Removing the unique hole leaves no vertices, hence P₀ is empty.
-- Recomposition has only a new hole vertex, no initial vertices, and no roots.
-- Its reachable part is therefore empty.
noncomputable def recomposed : SetSystem (WithHole alphabet 0) 0 :=
  trim { (atomic hole).graph with initial := ∅, root := ∅ }

theorem recomposed_no_vertices (v : recomposed.Vertex) : False := by
  classical
  have e := (Fintype.equivFin
    {v : Fin 1 // ({ (atomic hole).graph with initial := ∅, root := ∅ } :
      Presentation (WithHole alphabet 0) 0 (Fin 1)).Reachable v}).symm
  have h := (e v).property
  obtain ⟨_, hr, _⟩ := h
  exact hr.elim id id

theorem context_not_equivalent_to_recomposition :
    ¬ UnfoldEquivalent C.system recomposed := by
  rintro ⟨U, ⟨f, hf⟩, ⟨g, _⟩⟩
  have h0 : (⟨0, Nat.zero_lt_one⟩ : Fin 1) ∈ C.system.graph.initial := Set.mem_univ _
  obtain ⟨v, _, _⟩ := hf.1 _ h0
  exact recomposed_no_vertices (g.toFun v)

-- The same loss occurs at every hole rank, including the k ≥ 2 case
-- used in the extremal-context argument: all outgoing directions loop
-- back to the initial hole.
def loopingContext (k : ℕ) : SetContext alphabet k 0 where
  system := {
    size := 1
    graph := {
      label := fun _ => ⟨k, Sum.inr ⟨rfl⟩⟩
      initial := Set.univ
      root := ∅
      edge := fun _ d t => d < k ∧ t = Sum.inl (⟨0, Nat.zero_lt_one⟩ : Fin 1)
      direction_valid := fun _ _ _ h => h.1 }
    reachable := fun v => ⟨v, Or.inl (Set.mem_univ v), .refl⟩ }
  one_hole := by
    refine ⟨(⟨0, Nat.zero_lt_one⟩ : Fin 1), ⟨⟨rfl⟩, rfl⟩, ?_⟩
    intro v _
    exact Subsingleton.elim (α := Fin 1) v _

-- All k+1 unary pieces are empty after deleting their only vertex.
-- Thus the literal reconstruction has no initial vertices, roots, or edges.
def emptyPieceReconstruction (k : ℕ) : Presentation (WithHole alphabet k) 0 (Fin 1) where
  label := fun _ => ⟨k, Sum.inr ⟨rfl⟩⟩
  initial := ∅
  root := ∅
  edge := fun _ _ _ => False
  direction_valid := fun _ _ _ h => False.elim h

noncomputable def recomposedAtRank (k : ℕ) : SetSystem (WithHole alphabet k) 0 :=
  trim (emptyPieceReconstruction k)

theorem recomposedAtRank_no_vertices (k : ℕ) (v : (recomposedAtRank k).Vertex) : False := by
  classical
  let e := (Fintype.equivFin {v : Fin 1 // (emptyPieceReconstruction k).Reachable v}).symm
  obtain ⟨_, hr, _⟩ := (e v).property
  exact hr.elim id id

theorem looping_context_not_equivalent (k : ℕ) :
    ¬ UnfoldEquivalent (loopingContext k).system (recomposedAtRank k) := by
  rintro ⟨U, ⟨f, hf⟩, ⟨g, _⟩⟩
  have h0 : (⟨0, Nat.zero_lt_one⟩ : Fin 1) ∈ (loopingContext k).system.graph.initial :=
    Set.mem_univ _
  obtain ⟨v, _, _⟩ := hf.1 _ h0
  exact recomposedAtRank_no_vertices k (g.toFun v)

#print axioms context_not_equivalent_to_recomposition
#print axioms looping_context_not_equivalent
end ContextDecompositionAudit
