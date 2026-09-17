import Lax369799Proofs.AtomicFlattening
import Mathlib.Tactic.FinCases

/- Diagnostic for the inclusion (*) in the v6 syntactic continuity proof. -/
namespace YieldSubstitutionAudit
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

-- Direction 1 is missing at the initial vertex. Hence there are no
-- outer yields. The rooted inner letter nevertheless survives flattening.
def pattern : SetSystem (SetSystem A) 0 where
  size := 2
  graph := {
    label := Fin.cases ⟨2, empty A 2⟩ (fun _ => ⟨0, rootedLetter⟩)
    initial := {0}
    root := ∅
    edge := fun v d t => v = 0 ∧ d = 0 ∧ t = .inl 1
    direction_valid := by
      rintro v d t ⟨rfl, rfl, _⟩
      exact Nat.zero_lt_succ 1 }
  reachable := by
    intro v
    fin_cases v
    · exact ⟨0, Or.inl rfl, .refl⟩
    · exact ⟨0, Or.inl rfl, Relation.ReflTransGen.refl.tail ⟨0, rfl, rfl, rfl⟩⟩

theorem no_initial_yield (U : System (SetSystem A) 0) : ¬ InitYield pattern U := by
  rintro ⟨D, ⟨f⟩, _⟩
  obtain ⟨v, hv⟩ := D.property.1
  have hi : v ∈ D.val.graph.initial := by rw [hv]; rfl
  have he : f.toFun v = (0 : Fin 2) := f.initial v hi
  have hl : (D.val.graph.label v).1 = 2 := by
    rw [← f.label v, he]
    rfl
  obtain ⟨t, ht, _⟩ := D.property.2.2 v 1 (by rw [hl]; decide)
  have h := f.edge v 1 t ht
  exact (by decide : (1 : ℕ) ≠ 0) h.2.1

theorem no_yield (T : SetSystem (SetSystem A) 0) : ¬ Yield pattern T := by
  rintro (⟨U, hu, _⟩ | ⟨U, ⟨D, ⟨f⟩, _⟩, _⟩)
  · exact no_initial_yield U hu
  · obtain ⟨v, hv⟩ := D.property.1
    have hi := f.initial v (by rw [hv]; rfl)
    exact hi

private noncomputable abbrev G := Lax369799Proofs.Flattening.graph pattern

private theorem flattened_root : ∃ v : (flatten pattern).Vertex,
    (flatten pattern).graph.root v ∧ (flatten pattern).graph.label v = ⟨0, ()⟩ := by
  let w : (v : pattern.Vertex) × (Inner pattern v).Vertex := ⟨(1 : Fin 2), (0 : Fin 1)⟩
  have hr : G.root w := Or.inl (Or.inr True.intro)
  have hw : G.Reachable w := ⟨w, Or.inr hr, .refl⟩
  refine ⟨index G ⟨w, hw⟩, ?_, ?_⟩
  · change G.root (vertex G (index G ⟨w, hw⟩))
    rw [vertex_index]
    exact hr
  · change G.label (vertex G (index G ⟨w, hw⟩)) = _
    rw [vertex_index]
    rfl

theorem flattened_has_yield : Yield (flatten pattern) rootedLetter := by
  obtain ⟨w, hw, hl⟩ := flattened_root
  let H : Presentation A 0 (flatten pattern).Vertex :=
    { (flatten pattern).graph with initial := (flatten pattern).graph.root, root := ∅ }
  let f : Map (atomic (A := A) (n := 0) ()).graph H := {
    toFun := fun _ => w
    initial := fun _ _ => hw
    root := fun _ h => False.elim h
    label := fun _ => hl
    edge := by rintro v d t ⟨i, _, _⟩; exact Fin.elim0 i }
  let U : System A 0 := atomicSystem ()
  exact Or.inr ⟨U, ⟨U, ⟨lift f⟩, ⟨Lax369799Proofs.MorphismTheorems.identity _,
    Lax369799Proofs.MorphismTheorems.identity_surjective _⟩⟩, rfl⟩

theorem yield_substitution_inclusion_fails :
    ¬ (∀ R, Yield (flatten pattern) R →
      ∃ T, Yield pattern T ∧ Yield (flatten T) R) := by
  intro h
  obtain ⟨T, ht, _⟩ := h rootedLetter flattened_has_yield
  exact no_yield T ht

#print axioms yield_substitution_inclusion_fails
end YieldSubstitutionAudit
