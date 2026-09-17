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

#print axioms context_not_equivalent_to_recomposition
end ContextDecompositionAudit
