import Lax369799.FinitePathEvaluation
import Lax369799Proofs.FiniteBranchWords
import Lax369799Proofs.UntrimmedFlattening
import Mathlib.Tactic.FinCases

namespace Lax369799Proofs.FinitePathEvaluation
set_option backward.isDefEq.respectTransparency false
open Lax369799
open RankedSystems (RankedSet)
open FinitePresentations FiniteSyntacticAlgebra FiniteBranchWords

open Lax369799.FinitePathEvaluation

private theorem path_edge {A : RankedSet} {k : ℕ} (w : Fin k → A 1) (a : A 0)
    (v u : Fin (k + 1)) (d : ℕ) :
    (path w a).graph.edge v d (.inl u) ↔ v.val < k ∧ d = 0 ∧ u.val = v.val + 1 := by
  constructor
  · rintro ⟨i, rfl, rfl, h⟩
    cases h
    exact ⟨i.isLt, rfl, rfl⟩
  · rintro ⟨hv, rfl, hu⟩
    exact ⟨⟨v.val, hv⟩, Fin.ext rfl, rfl, congrArg Sum.inl (Fin.ext hu)⟩

private abbrev Raw {A : RankedSet} {k : ℕ} (w : Fin (k + 1) → A 1) (a : A 0) :=
  (v : (application (atomic (w 0)) (path (fun i => w i.succ) a)).Vertex) ×
    (Inner (application (atomic (w 0)) (path (fun i => w i.succ) a)).graph v).Vertex

private def prefixEquiv {A : RankedSet} {k : ℕ} (w : Fin (k + 1) → A 1) (a : A 0) :
    Raw w a ≃ Fin (k + 2) where
  toFun := fun v => Fin.cases (fun _ => 0) (fun _ u => u.succ) v.1 v.2
  invFun := Fin.cases ⟨(0 : Fin 2), (0 : Fin 1)⟩ (fun u => ⟨(1 : Fin 2), u⟩)
  left_inv := by
    rintro ⟨v, u⟩
    fin_cases v
    · fin_cases u; rfl
    · rfl
  right_inv := by intro v; cases v using Fin.cases <;> rfl

private def prefixIso {A : RankedSet} {k : ℕ} (w : Fin (k + 1) → A 1) (a : A 0) :
    PresentationIso (flattenPresentation (application (atomic (w 0)) (path (fun i => w i.succ) a)).graph)
      (path w a).graph where
  vertex := prefixEquiv w a
  label := by
    rintro ⟨v, u⟩
    fin_cases v
    · fin_cases u
      change Fin.lastCases (motive := fun _ => RankedSystems.Symbol A) ⟨0, a⟩ (fun i => ⟨1, w i⟩) (Fin.castSucc (0 : Fin (k + 1))) = _
      exact Fin.lastCases_castSucc (0 : Fin (k + 1))
    · change Fin.lastCases (motive := fun _ => RankedSystems.Symbol A) ⟨0, a⟩ (fun i => ⟨1, w i⟩) u.succ =
        Fin.lastCases (motive := fun _ => RankedSystems.Symbol A) ⟨0, a⟩ (fun i => ⟨1, w i.succ⟩) u
      cases u using Fin.lastCases with
      | last => simp
      | cast i => change Fin.lastCases (motive := fun _ => RankedSystems.Symbol A) _ _ i.succ.castSucc = _; simp only [Fin.lastCases_castSucc]
  initial := by
    rintro ⟨v, u⟩
    fin_cases v
    · fin_cases u; exact ⟨fun _ => ⟨rfl, True.intro⟩, fun _ => rfl⟩
    · change u.succ = 0 ↔ (1 : Fin 2) = 0 ∧ _
      simp
  root := by
    rintro ⟨v, u⟩
    fin_cases v <;> exact ⟨False.elim, fun h => h.elim id (fun h => h.1)⟩
  edge := by
    rintro ⟨v, u⟩ d t
    cases t with
    | inr j => exact Fin.elim0 j
    | inl z =>
      obtain ⟨q, z⟩ := z
      fin_cases v
      · fin_cases u
        fin_cases q
        · fin_cases z
          change (path w a).graph.edge (0 : Fin (k + 2)) d (.inl (0 : Fin (k + 2))) ↔ _
          rw [path_edge]
          simp [flattenPresentation, Inner, application, atomic, ofSetSystem,
            RankedSystems.atomic, Fin.exists_fin_one]
        · change (path w a).graph.edge (0 : Fin (k + 2)) d (.inl z.succ) ↔ _
          rw [path_edge]
          simp [flattenPresentation, Inner, application, atomic, ofSetSystem,
            RankedSystems.atomic, Fin.exists_fin_one, Fin.exists_fin_two]
          intro _
          change z.val = 0 ↔ z = (0 : Fin (k + 1))
          exact ⟨fun h => Fin.ext h, fun h => congrArg Fin.val h⟩
      · fin_cases q
        · fin_cases z
          change (path w a).graph.edge u.succ d (.inl (0 : Fin (k + 2))) ↔ _
          rw [path_edge]
          simp [flattenPresentation, Inner, application, path]
        · change (path w a).graph.edge u.succ d (.inl z.succ) ↔ _
          rw [path_edge]
          simp [flattenPresentation, Inner, application, path]
          exact (path_edge _ _ u z d).symm

/--
---
conclusion: Lax369799.FinitePathEvaluation.evaluation
---
Separate the first vertex by the flattening isomorphism. Associativity
reduces its suffix to a value, and induction gives the word evaluation.
-/
theorem evaluation {A : RankedSet} (E : Algebra A) {k : ℕ}
    (w : Fin k → A 1) (a : A 0) :
    E.eval 0 (path w a) = value E (List.ofFn w) a := by
  induction k with
  | zero =>
    have hi : Isomorphic (path w a) (atomic a) := by
      refine ⟨{ vertex := Equiv.refl (Fin 1)
                label := ?_
                initial := ?_
                root := fun _ => Iff.rfl
                edge := ?_ }⟩
      · intro v; fin_cases v
        change (⟨0, a⟩ : RankedSystems.Symbol A) =
          Fin.lastCases ⟨0, a⟩ (fun i => ⟨1, w i⟩) (Fin.last 0)
        exact (Fin.lastCases_last (motive := fun _ : Fin 1 => RankedSystems.Symbol A)
          (last := ⟨0, a⟩) (cast := fun i => ⟨1, w i⟩)).symm
      · intro v; fin_cases v
        exact ⟨fun _ => rfl, fun _ => True.intro⟩
      · intro v d t
        simp [path, atomic, ofSetSystem, RankedSystems.atomic]
    simpa [value] using (E.isomorphic _ _ _ hi).trans (E.unit 0 a)
  | succ k ih =>
    have hi : Isomorphic (flatten (application (atomic (w 0)) (path (fun i => w i.succ) a)))
        (path w a) :=
      ⟨UntrimmedFlattening.isoTrans
        (UntrimmedFlattening.isoSymm (UntrimmedFlattening.reindexIso _ (Fintype.equivFin _)))
        (prefixIso w a)⟩
    have he : relabel E.eval (application (atomic (w 0)) (path (fun i => w i.succ) a)) =
        application (w 0) (E.eval 0 (path (fun i => w i.succ) a)) := by
      dsimp only [relabel, application]
      congr 1
      congr 1
      funext v
      fin_cases v
      · exact congrArg (Sigma.mk 1) (E.unit 1 (w 0))
      · rfl
    rw [← E.isomorphic _ _ _ hi, ← E.associative, he, ih]
    rw [List.ofFn_succ]
    rfl

end Lax369799Proofs.FinitePathEvaluation
