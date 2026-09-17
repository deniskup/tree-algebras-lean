import Lax369799Proofs.AtomicFlattening
import Mathlib.Tactic.FinCases

/- A local diagnostic for reachability pruning in the v6 monad lemma.
   This is not an Archive statement. -/
namespace FlatteningAssociativityAudit
open Lax369799.RankedSystems Lax369799.Morphisms Lax369799.Flattening
open Lax369799Proofs.Pullbacks

abbrev A : RankedSet := fun _ => Unit

def empty (B : RankedSet) (n : ℕ) : SetSystem B n where
  size := 0
  graph := {
    label := Fin.elim0
    initial := ∅
    root := ∅
    edge := fun _ _ _ => False
    direction_valid := fun v => Fin.elim0 v }
  reachable := fun v => Fin.elim0 v

def rootedLetter : SetSystem A 0 := plant (atomic ())

-- The outer edge makes vertex 1 reachable, even though vertex 0's
-- middle-level label is the empty set-system of rank 1.
def nested : SetSystem (SetSystem (SetSystem A)) 0 where
  size := 2
  graph := {
    label := Fin.cases ⟨1, empty (SetSystem A) 1⟩ (fun _ => ⟨0, atomic rootedLetter⟩)
    initial := {0}
    root := ∅
    edge := fun v d t => v = 0 ∧ d = 0 ∧ t = .inl 1
    direction_valid := by
      rintro v d t ⟨rfl, rfl, _⟩
      exact Nat.zero_lt_one }
  reachable := by
    intro v
    fin_cases v
    · exact ⟨0, Or.inl rfl, .refl⟩
    · exact ⟨0, Or.inl rfl, Relation.ReflTransGen.refl.tail ⟨0, rfl, rfl, rfl⟩⟩

private noncomputable abbrev middleGraph := Lax369799Proofs.Flattening.graph nested

theorem middle_has_no_vertices (v : (flatten nested).Vertex) : False := by
  obtain ⟨r, hr, _⟩ := ((index middleGraph).symm v).property
  obtain ⟨r, u⟩ := r
  fin_cases r
  · exact Fin.elim0 u
  · rcases hr with ⟨h, _⟩ | h | ⟨h, _⟩
    · exact (by decide : (1 : Fin 2) ≠ 0) h
    · exact h
    · exact h

noncomputable def outerFirst := flatten (flatten nested)
noncomputable def innerFirst := flatten (relabel (fun _ S => flatten S) nested)

theorem outerFirst_has_no_vertices (v : outerFirst.Vertex) : False := by
  exact middle_has_no_vertices
    (vertex (Lax369799Proofs.Flattening.graph (flatten nested)) v).1

theorem innerFirst_has_root : ∃ v : innerFirst.Vertex, v ∈ innerFirst.graph.root := by
  have hr : (0 : Fin 1) ∈ rootedLetter.graph.root := Or.inr True.intro
  obtain ⟨f, hf⟩ := Lax369799Proofs.AtomicFlattening.outer_atomic_cover rootedLetter
  obtain ⟨u, hu, _⟩ := hf.2.1 (0 : Fin 1) hr
  let G := Lax369799Proofs.Flattening.graph (relabel (fun _ S => flatten S) nested)
  let w : (v : (relabel (fun _ S => flatten S) nested).Vertex) ×
      (Inner (relabel (fun _ S => flatten S) nested) v).Vertex := ⟨(1 : Fin 2), u⟩
  have hw : G.root w := Or.inl hu
  have reach : G.Reachable w := ⟨w, Or.inr hw, .refl⟩
  refine ⟨index G ⟨w, reach⟩, ?_⟩
  change G.root (vertex G (index G ⟨w, reach⟩))
  rw [vertex_index]
  exact hw

theorem flattening_not_associative_up_to_unfolding :
    ¬ UnfoldEquivalent outerFirst innerFirst := by
  rintro ⟨U, ⟨f, _⟩, ⟨g, hg⟩⟩
  obtain ⟨r, hr⟩ := innerFirst_has_root
  obtain ⟨v, _, _⟩ := hg.2.1 r hr
  exact outerFirst_has_no_vertices (f.toFun v)

#print axioms flattening_not_associative_up_to_unfolding
end FlatteningAssociativityAudit
