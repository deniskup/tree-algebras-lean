import Lax369799.ClosedUnaryLift
import Lax369799Proofs.UntrimmedFlattening
import Mathlib.Tactic.FinCases

namespace Lax369799Proofs.ClosedUnaryLift
open Lax369799.RankedSystems (RankedSet)
open Lax369799.FinitePresentations Lax369799.FiniteSyntacticAlgebra Lax369799.ClosedUnaryLift

private def swap {A : RankedSet} (initial : Bool) (c d : A 0) :
    ((v : (system initial (binary c d)).Vertex) ×
      (Inner (system initial (binary c d)).graph v).Vertex) ≃
    ((v : (binary (system initial c) (system initial d)).Vertex) ×
      (Inner (binary (system initial c) (system initial d)).graph v).Vertex) where
  toFun := fun v => Fin.cases ⟨(0 : Fin 2), (0 : Fin 1)⟩
    (fun _ => ⟨(1 : Fin 2), (0 : Fin 1)⟩) v.2
  invFun := fun v => ⟨(0 : Fin 1), v.1⟩
  left_inv := by rintro ⟨v, w⟩; fin_cases v; fin_cases w <;> rfl
  right_inv := by rintro ⟨v, w⟩; fin_cases v <;> fin_cases w <;> rfl

private def graphIso {A : RankedSet} (initial : Bool) (c d : A 0) :
    PresentationIso (flattenPresentation (system initial (binary c d)).graph)
      (flattenPresentation (binary (system initial c) (system initial d)).graph) where
  vertex := swap initial c d
  label := by rintro ⟨v, w⟩; fin_cases v; fin_cases w <;> rfl
  initial := by
    rintro ⟨v, w⟩
    fin_cases v; fin_cases w
    all_goals change (True ∧ initial = true) ↔ (initial = true ∧ True); tauto
  root := by
    rintro ⟨v, w⟩
    fin_cases v; fin_cases w
    all_goals change (False ∨ False ∧ _) ↔ (False ∨ False ∧ _); simp
  edge := by
    rintro ⟨v, w⟩ e t
    fin_cases v; fin_cases w
    all_goals
      constructor
      · intro h
        have hh := (flattenPresentation (binary (system initial c) (system initial d)).graph).direction_valid _ e _ h
        change e < 0 at hh
        omega
      · intro h
        have hh := (flattenPresentation (system initial (binary c d)).graph).direction_valid _ e _ h
        change e < 0 at hh
        omega

/--
---
conclusion: Lax369799.ClosedUnaryLift.preserves_sum
---
Expanding a nullary sum in a marked singleton gives the same two vertices
as summing the two lifted singletons. No pruning is used.
-/
theorem preserves_sum {A : RankedSet} (E : Algebra A) (initial : Bool) (c d : A 0) :
    value E initial (sumValue E c d) = sumValue E (value E initial c) (value E initial d) := by
  have hl : relabel E.eval (system initial (binary c d)) = system initial (sumValue E c d) := rfl
  have hr : relabel E.eval (binary (system initial c) (system initial d)) =
      binary (value E initial c) (value E initial d) := by
    dsimp only [relabel, binary, value]
    congr 1
    congr 1
    funext v
    fin_cases v <;> rfl
  change E.eval 1 (system initial (sumValue E c d)) = E.eval 1 (binary _ _)
  rw [← hl, E.associative, ← hr, E.associative]
  apply E.isomorphic
  exact ⟨UntrimmedFlattening.isoTrans
    (UntrimmedFlattening.isoSymm (UntrimmedFlattening.reindexIso _ (Fintype.equivFin _)))
    (UntrimmedFlattening.isoTrans (graphIso initial c d)
      (UntrimmedFlattening.reindexIso _ (Fintype.equivFin _)))⟩

end Lax369799Proofs.ClosedUnaryLift
