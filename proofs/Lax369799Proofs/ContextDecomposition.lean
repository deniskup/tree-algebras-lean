import Lax369799.ContextDecomposition
import Lax369799Proofs.PresentationCovers

namespace Lax369799Proofs.ContextDecomposition
open Lax369799.RankedSystems Lax369799.Morphisms Lax369799.Flattening
open Lax369799.PresentationCovers Lax369799.ContextDecomposition

theorem hole_label {A : RankedSet} {k : ℕ} (C : SetContext A k 0) :
    C.system.graph.label (holeVertex C) = ⟨k, Sum.inr ⟨rfl⟩⟩ := by
  have H : IsHole (C.system.graph.label (holeVertex C)) := (Classical.choose_spec C.one_hole).1
  generalize C.system.graph.label (holeVertex C) = a at H ⊢
  rcases a with ⟨r, a⟩
  obtain ⟨⟨hr⟩, ha⟩ := H
  change k = r at hr
  subst r
  change a = Sum.inr ⟨rfl⟩ at ha
  exact congrArg (Sigma.mk k) ha

/--
---
conclusion: Lax369799.ContextDecomposition.piece_has_no_hole
---
Every copied vertex differs from the unique hole vertex.
-/
theorem piece_has_no_hole {A : RankedSet} {k : ℕ} (C : SetContext A k 0)
    (i : Fin (k + 1)) (v : BodyVertex C) : ¬ IsHole ((piece C i).label v) := by
  intro hv
  exact v.property ((Classical.choose_spec C.one_hole).2 v.val hv)

private noncomputable def project {A : RankedSet} {k : ℕ} (C : SetContext A k 0) :
    CopyVertex k (BodyVertex C) → C.system.Vertex
  | none => holeVertex C
  | some (_, v) => v.val

private noncomputable def reconstructionCover {A : RankedSet} {k : ℕ}
    (C : SetContext A k 0) :
    Cover (recomposePresentation (boundary C) (piece C)) C.system.graph where
  toFun := project C
  label := by
    intro v
    cases v with
    | none => exact hole_label C
    | some v => rfl
  initial := by
    intro v hv
    cases v with
    | none => exact hv
    | some v =>
      rcases v with ⟨i, v⟩
      rcases hv with ⟨hi, hv⟩
      subst i
      rcases hv with ⟨_, hv⟩ | ⟨d, hd, _⟩
      · exact hv
      · exact False.elim (Fin.succ_ne_zero d hd.symm)
  root := by
    intro v hv
    cases v <;> exact hv
  edge := by
    intro v d t ht
    cases t with
    | inr j => exact Fin.elim0 j
    | inl w =>
      cases v with
      | none =>
        cases w with
        | none => obtain ⟨i, rfl, hi⟩ := ht; exact hi
        | some w =>
          rcases w with ⟨j, w⟩
          obtain ⟨i, rfl, rfl, hw⟩ := ht
          rcases hw with ⟨hi, _⟩ | ⟨j, hj, he⟩
          · exact False.elim (Fin.succ_ne_zero i hi)
          · have h : i = j := Fin.succ_inj.mp hj
            subst j
            exact he
      | some v =>
        cases w with
        | none => exact ht
        | some w => exact ht.2
  initial_lift := by
    intro w hw
    by_cases h : w = holeVertex C
    · subst w
      exact ⟨none, hw, rfl⟩
    · exact ⟨some (0, ⟨w, h⟩), ⟨rfl, Or.inl ⟨rfl, hw⟩⟩, rfl⟩
  root_lift := by
    intro w hw
    by_cases h : w = holeVertex C
    · subst w
      exact ⟨none, hw, rfl⟩
    · exact ⟨some (0, ⟨w, h⟩), hw, rfl⟩
  edge_lift := by
    intro v d t ht
    cases t with
    | inr j => exact Fin.elim0 j
    | inl w =>
      cases v with
      | none =>
        have hd : d < k := by
          have h := C.system.graph.direction_valid (holeVertex C) d (.inl w) ht
          simpa only [hole_label C] using h
        by_cases hw : w = holeVertex C
        · subst w
          exact ⟨.inl none, ⟨⟨d, hd⟩, rfl, ht⟩, rfl⟩
        · exact ⟨.inl (some ((⟨d, hd⟩ : Fin k).succ, ⟨w, hw⟩)),
            ⟨⟨d, hd⟩, rfl, rfl, Or.inr ⟨⟨d, hd⟩, rfl, ht⟩⟩, rfl⟩
      | some v =>
        by_cases hw : w = holeVertex C
        · subst w
          exact ⟨.inl none, ht, rfl⟩
        · exact ⟨.inl (some (v.1, ⟨w, hw⟩)), ⟨rfl, ht⟩, rfl⟩

/--
---
conclusion: Lax369799.ContextDecomposition.decomposition_cover
---
Map each copied vertex to its original and the new hole to the original
hole. Every initial vertex, root, and successor has a preimage, including
initial/root holes and hole self-loops. Restrict this cover to reachable
vertices.
-/
theorem decomposition_cover {A : RankedSet} {k : ℕ} (C : SetContext A k 0) :
    UnfoldsTo C.system (recompose C) := by
  classical
  exact Lax369799Proofs.trim_cover _ _ (reconstructionCover C)

/--
---
conclusion: Lax369799.ContextDecomposition.decomposition_equivalence
---
The recomposition itself is a common cover of the original and recomposed
systems: use the projection to the former and the identity to the latter.
-/
theorem decomposition_equivalence {A : RankedSet} {k : ℕ} (C : SetContext A k 0) :
    UnfoldEquivalent C.system (recompose C) := by
  refine ⟨recompose C, decomposition_cover C, ?_⟩
  let T := recompose C
  let f : Morphism T T := {
    toFun := id
    label := fun _ => rfl
    initial := fun _ h => h
    root := fun _ h => h
    edge := by intro v d t h; cases t <;> exact h }
  refine ⟨f, ?_, ?_, ?_⟩
  · intro w hw; exact ⟨w, hw, rfl⟩
  · intro w hw; exact ⟨w, hw, rfl⟩
  · intro v d t ht
    refine ⟨t, ht, ?_⟩
    cases t <;> rfl

end Lax369799Proofs.ContextDecomposition
