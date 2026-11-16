import Lax369799.SelectedChoicePreservation
import Lax369799Proofs.ChoicePreservingUnary
import Lax369799Proofs.FiniteBranchWords
import Lax369799Proofs.UnaryTestContexts
import Lax369799Proofs.ExtremalUnaryTypes
import Lax369799Proofs.FiniteSums
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic.NormNum

namespace Lax369799Proofs.SelectedChoicePreservation
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open Lax369799.RankedSystems (RankedSet)
open Lax369799.FinitePresentations Lax369799.FiniteSyntacticAlgebra
open Lax369799.FiniteContextualOrder Lax369799.FiniteAcceptance
open Lax369799.UnaryTestContexts

private def piece {A : RankedSet} (initial : Bool) (t : A 1) (c : A 0) : FiniteSystem A 1 where
  size := 2
  graph := {
    label := Fin.cases ⟨1, t⟩ (fun _ => ⟨0, c⟩)
    initial := fun v => v = 1 ∧ initial = true
    root := {0}
    edge := fun v d s => v = 0 ∧ d = 0 ∧ s = .inr 0
    direction_valid := by rintro v d s ⟨rfl, rfl, _⟩; exact Nat.zero_lt_one }

private def pieceIso {A : RankedSet} (initial : Bool) (t : A 1) (c : A 0) :
    PresentationIso (sumPresentation (plant (atomic t)).graph
      (Lax369799.ClosedUnaryLift.system initial c).graph) (piece initial t c).graph where
  vertex := finSumFinEquiv
  label := by intro v; cases v with
              | inl v => fin_cases v; rfl
              | inr v => fin_cases v; rfl
  initial := by
    intro v
    cases v with
    | inl v => fin_cases v; change ((0 : Fin 2) = 1 ∧ initial = true) ↔ False; simp
    | inr v => fin_cases v; change ((1 : Fin 2) = 1 ∧ initial = true) ↔ initial = true; simp
  root := by
    intro v
    cases v with
    | inl v => fin_cases v; change ((0 : Fin 2) = 0) ↔ (False ∨ True); simp
    | inr v => fin_cases v; change ((1 : Fin 2) = 0) ↔ False; simp
  edge := by
    intro v d s
    cases v with
    | inl v =>
      fin_cases v
      change ((0 : Fin 2) = 0 ∧ d = 0 ∧ Sum.map finSumFinEquiv id s = .inr 0) ↔
        ∃ z, (∃ i : Fin 1, d = i.val ∧ z = .inr i) ∧ s = Sum.map Sum.inl id z
      cases s with
      | inl w => cases w <;> simp
      | inr i => fin_cases i; simp
    | inr v =>
      fin_cases v
      change ((1 : Fin 2) = 0 ∧ d = 0 ∧ _) ↔ ∃ z, False ∧ _
      simp

private theorem eval_piece {A : RankedSet} (E : Algebra A) (initial : Bool) (t : A 1) (c : A 0) :
    E.eval 1 (piece initial t c) = sumValue E (E.eval 1 (plant (atomic t)))
      (Lax369799.ClosedUnaryLift.value E initial c) := by
  let P := plant (atomic t)
  let Q := Lax369799.ClosedUnaryLift.system initial c
  have hi : Isomorphic (sum P Q) (piece initial t c) :=
    ⟨UntrimmedFlattening.isoTrans
      (UntrimmedFlattening.isoSymm (UntrimmedFlattening.reindexIso _ (Fintype.equivFin _)))
      (pieceIso initial t c)⟩
  have hr : relabel E.eval (binary P Q) = binary (E.eval 1 P) (E.eval 1 Q) := by
    dsimp only [relabel, binary]
    congr 1
    congr 1
    funext v
    fin_cases v <;> rfl
  exact (E.isomorphic _ _ _ hi).symm.trans
    ((E.isomorphic _ _ _ (FiniteSums.flatten_binary P Q)).symm.trans
      ((E.associative _ _).symm.trans (congrArg (E.eval 1) hr)))

private def test {A : RankedSet} (root : Prop) (t b : A 1) (c : A 0) : FiniteSystem A 0 where
  size := 3
  graph := {
    label := Fin.cases ⟨1, b⟩ (Fin.cases ⟨1, t⟩ (fun _ => ⟨0, c⟩))
    initial := ∅
    root := fun v => v = 1 ∨ (v = 0 ∧ root)
    edge := fun v d s => d = 0 ∧ ((v = 0 ∧ s = .inl (2 : Fin 3)) ∨ (v = 1 ∧ s = .inl (0 : Fin 3)))
    direction_valid := by
      rintro v d s ⟨rfl, h⟩
      rcases h with ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> exact Nat.zero_lt_one }

private def pattern {A : RankedSet} (root : Prop) (t b : A 1) (c : A 0) :
    FiniteSystem (FiniteSystem A) 0 where
  size := 3
  graph := {
    label := Fin.cases ⟨1, atomic b⟩
      (Fin.cases ⟨1, piece false t c⟩ (fun _ => ⟨1, piece true t c⟩))
    initial := ∅
    root := fun v => v = 1 ∨ (v = 0 ∧ root)
    edge := fun v d s => d = 0 ∧ ((v = 0 ∧ s = .inl (2 : Fin 3)) ∨ (v ≠ 0 ∧ s = .inl (0 : Fin 3)))
    direction_valid := by
      rintro v d s ⟨rfl, _⟩
      fin_cases v <;> exact Nat.zero_lt_one }

private abbrev Raw {A : RankedSet} (root : Prop) (t b : A 1) (c : A 0) :=
  (v : (pattern root t b c).Vertex) × (Inner (pattern root t b c).graph v).Vertex

private def project {A : RankedSet} (root : Prop) (t b : A 1) (c : A 0) :
    Raw root t b c → Fin 3 := fun v =>
  Fin.cases (fun _ => 0) (fun _ w => if w.val = 0 then 1 else 2) v.1 v.2

private def testCover {A : RankedSet} (root : Prop) (t b : A 1) (c : A 0) :
    Lax369799.PresentationCovers.Cover (flattenPresentation (pattern root t b c).graph)
      (test root t b c).graph where
  toFun := project root t b c
  label := by rintro ⟨v, w⟩; fin_cases v <;> fin_cases w <;> rfl
  initial := by rintro v ⟨h, _⟩; exact False.elim h
  root := by
    rintro ⟨v, w⟩ h
    fin_cases v <;> fin_cases w
    · rcases h with h | ⟨h, _⟩
      · exact False.elim h
      · rcases h with h | ⟨_, hr⟩
        · exact False.elim ((by decide : (0 : Fin 3) ≠ 1) h)
        · exact Or.inr ⟨rfl, hr⟩
    · exact Or.inl rfl
    · rcases h with h | ⟨_, hi⟩
      · exact False.elim ((by decide : (1 : Fin 2) ≠ 0) h)
      · exact Bool.noConfusion hi.2
    · exact Or.inl rfl
    · rcases h with h | ⟨h, _⟩
      · exact False.elim ((by decide : (1 : Fin 2) ≠ 0) h)
      · rcases h with h | ⟨h, _⟩
        · exact False.elim ((by decide : (2 : Fin 3) ≠ 1) h)
        · exact False.elim ((by decide : (2 : Fin 3) ≠ 0) h)
  edge := by
    rintro ⟨v, w⟩ d s (⟨u, hu, rfl⟩ | ⟨j, hj, hh⟩)
    · fin_cases v
      · obtain ⟨i, _, he⟩ := hu
        cases he
      · obtain ⟨_, _, he⟩ := hu
        cases he
      · obtain ⟨_, _, he⟩ := hu
        cases he
    · rcases hh with ⟨⟨q, u⟩, hed, hin, rfl⟩ | ⟨l, _, _⟩
      · fin_cases v
        · fin_cases j
          obtain ⟨i, hd, _⟩ := hj
          fin_cases i
          have hq : q = (2 : Fin 3) := by
            change (0 : ℕ) = 0 ∧ (((0 : Fin 3) = 0 ∧ Sum.inl q = Sum.inl (2 : Fin 3)) ∨
              (0 ≠ 0 ∧ Sum.inl q = Sum.inl (0 : Fin 3))) at hed
            simpa using hed
          subst q
          have hu : u = (1 : Fin 2) := hin.1
          subst u
          exact ⟨hd, Or.inl ⟨rfl, rfl⟩⟩
        · fin_cases j
          obtain ⟨hw, hd, _⟩ := hj
          change w = (0 : Fin 2) at hw
          subst w
          have hq : q = (0 : Fin 3) := by
            change (0 : ℕ) = 0 ∧ (((1 : Fin 3) = 0 ∧ Sum.inl q = Sum.inl (2 : Fin 3)) ∨
              (1 ≠ 0 ∧ Sum.inl q = Sum.inl (0 : Fin 3))) at hed
            simpa using hed
          subst q
          exact ⟨hd, Or.inr ⟨rfl, rfl⟩⟩
        · fin_cases j
          obtain ⟨hw, hd, _⟩ := hj
          change w = (0 : Fin 2) at hw
          subst w
          have hq : q = (0 : Fin 3) := by
            change (0 : ℕ) = 0 ∧ (((2 : Fin 3) = 0 ∧ Sum.inl q = Sum.inl (2 : Fin 3)) ∨
              (2 ≠ 0 ∧ Sum.inl q = Sum.inl (0 : Fin 3))) at hed
            simpa using hed
          subst q
          exact ⟨hd, Or.inr ⟨rfl, rfl⟩⟩
      · exact Fin.elim0 l
  initial_lift := by intro v h; exact False.elim h
  root_lift := by
    intro v h
    rcases h with rfl | ⟨rfl, h⟩
    · exact ⟨⟨(1 : Fin 3), (0 : Fin 2)⟩, Or.inl rfl, rfl⟩
    · exact ⟨⟨(0 : Fin 3), (0 : Fin 1)⟩, Or.inr ⟨Or.inr ⟨rfl, h⟩, trivial⟩, rfl⟩
  edge_lift := by
    rintro ⟨v, w⟩ d s h
    change d = 0 ∧ ((project root t b c ⟨v, w⟩ = 0 ∧ s = .inl (2 : Fin 3)) ∨
      (project root t b c ⟨v, w⟩ = 1 ∧ s = .inl (0 : Fin 3))) at h
    fin_cases v <;> fin_cases w
    · change d = 0 ∧ (((0 : Fin 3) = 0 ∧ s = .inl (2 : Fin 3)) ∨ (0 = 1 ∧ s = .inl (0 : Fin 3))) at h
      simp only [zero_ne_one, false_and, or_false, true_and] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨.inl ⟨(2 : Fin 3), (1 : Fin 2)⟩,
        Or.inr ⟨(0 : Fin 1), ⟨(0 : Fin 1), rfl, rfl⟩,
          Or.inl ⟨⟨(2 : Fin 3), (1 : Fin 2)⟩, ⟨rfl, Or.inl ⟨rfl, rfl⟩⟩,
            ⟨rfl, rfl⟩, rfl⟩⟩, rfl⟩
    · change d = 0 ∧ (((1 : Fin 3) = 0 ∧ s = .inl (2 : Fin 3)) ∨ (1 = 1 ∧ s = .inl (0 : Fin 3))) at h
      simp only [one_ne_zero, false_and, false_or, true_and] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨.inl ⟨(0 : Fin 3), (0 : Fin 1)⟩,
        Or.inr ⟨(0 : Fin 1), ⟨rfl, rfl, rfl⟩,
          Or.inl ⟨⟨(0 : Fin 3), (0 : Fin 1)⟩, ⟨rfl, Or.inr ⟨(by decide : (1 : Fin 3) ≠ 0), rfl⟩⟩,
            trivial, rfl⟩⟩, rfl⟩
    · change d = 0 ∧ (((2 : Fin 3) = 0 ∧ _) ∨ (2 = 1 ∧ _)) at h
      have h20 : (2 : Fin 3) ≠ 0 := by decide
      have h21 : (2 : Fin 3) ≠ 1 := by decide
      simp only [h20, h21, false_and, or_self] at h
      exact False.elim h.2
    · change d = 0 ∧ (((1 : Fin 3) = 0 ∧ s = .inl (2 : Fin 3)) ∨ (1 = 1 ∧ s = .inl (0 : Fin 3))) at h
      simp only [one_ne_zero, false_and, false_or, true_and] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨.inl ⟨(0 : Fin 3), (0 : Fin 1)⟩,
        Or.inr ⟨(0 : Fin 1), ⟨rfl, rfl, rfl⟩,
          Or.inl ⟨⟨(0 : Fin 3), (0 : Fin 1)⟩, ⟨rfl, Or.inr ⟨(by decide : (2 : Fin 3) ≠ 0), rfl⟩⟩,
            trivial, rfl⟩⟩, rfl⟩
    · change d = 0 ∧ (((2 : Fin 3) = 0 ∧ _) ∨ (2 = 1 ∧ _)) at h
      have h20 : (2 : Fin 3) ≠ 0 := by decide
      have h21 : (2 : Fin 3) ≠ 1 := by decide
      simp only [h20, h21, false_and, or_self] at h
      exact False.elim h.2

private theorem normal_form {A : RankedSet} (L : Lax369799.Algebras.Language A)
    (E : Algebra (Carrier (Accepting L)))
    (hE : ∀ n (S : FiniteSystem (FiniteSystem A) n),
      E.eval n (relabel (quotientMap (Accepting L)) S) = quotientMap (Accepting L) n (flatten S))
    (root : Prop) (t b : Carrier (Accepting L) 1) (c : Carrier (Accepting L) 0) :
    Lax369799.FiniteExtremal.value E b (data E root t c) = E.eval 0 (test root t b c) := by
  classical
  let C := Lax369799.FiniteNormalForms.normalContext (data E root t c).1 (data E root t c).2
  let P := relabel (Lax369799.FiniteContexts.substitution (atomic b)) C.system
  have hi : Isomorphic (relabel E.eval P) (relabel E.eval (pattern root t b c)) := by
    refine ⟨{
      vertex := Equiv.refl (Fin 3)
      label := ?_
      initial := fun _ => Iff.rfl
      root := fun _ => Iff.rfl
      edge := ?_ }⟩
    · intro v
      fin_cases v
      · rfl
      · change (⟨1, E.eval 1 (piece false t c)⟩ : Lax369799.RankedSystems.Symbol _) =
          ⟨1, E.eval 1 (atomic ((data E root t c).2 0))⟩
        rw [E.unit, eval_piece]
        rfl
      · change (⟨1, E.eval 1 (piece true t c)⟩ : Lax369799.RankedSystems.Symbol _) =
          ⟨1, E.eval 1 (atomic ((data E root t c).2 1))⟩
        rw [E.unit, eval_piece]
        rfl
    · intro v d s
      fin_cases v
      all_goals
        change (pattern root t b c).graph.edge _ d (Sum.map id id s) ↔ _
        rw [Sum.map_id_id]
        dsimp [pattern, P, C, Lax369799.FiniteNormalForms.normalContext,
          Lax369799.ExtremalContexts.normalContext, Lax369799.ExtremalContexts.normalSystem,
          Lax369799.ExtremalContexts.normalPresentation, relabel, ofSetSystem, data]
        simp [Fin.exists_fin_one] <;> rfl
  let f := FiniteCovers.compose
    (FiniteCovers.isoCover (UntrimmedFlattening.isoSymm
      (UntrimmedFlattening.reindexIso (flattenPresentation (pattern root t b c).graph) (Fintype.equivFin _))))
    (testCover root t b c)
  have hf : Function.Surjective f.toFun := by
    intro v
    fin_cases v
    · exact ⟨Fintype.equivFin _ ⟨(0 : Fin 3), (0 : Fin 1)⟩, by
        change project root t b c ((Fintype.equivFin _).symm (Fintype.equivFin _ _)) = _
        rw [Equiv.symm_apply_apply]; rfl⟩
    · exact ⟨Fintype.equivFin _ ⟨(1 : Fin 3), (0 : Fin 2)⟩, by
        change project root t b c ((Fintype.equivFin _).symm (Fintype.equivFin _ _)) = _
        rw [Equiv.symm_apply_apply]; rfl⟩
    · exact ⟨Fintype.equivFin _ ⟨(1 : Fin 3), (1 : Fin 2)⟩, by
        change project root t b c ((Fintype.equivFin _).symm (Fintype.equivFin _ _)) = _
        rw [Equiv.symm_apply_apply]; rfl⟩
  change E.eval 0 (flatten P) = _
  rw [← E.associative]
  exact (E.isomorphic _ _ _ hi).trans ((E.associative _ _).trans
    (FiniteOuterMorphisms.evaluation_cover L E hE f hf))

private def closedTest {A : RankedSet} (root : Prop) (t : A 1) (c : A 0) : FiniteSystem A 0 where
  size := 2
  graph := {
    label := Fin.cases ⟨0, c⟩ (fun _ => ⟨1, t⟩)
    initial := ∅
    root := fun v => v = 1 ∨ (v = 0 ∧ root)
    edge := fun v d s => v = 1 ∧ d = 0 ∧ s = .inl 0
    direction_valid := by rintro v d s ⟨rfl, rfl, _⟩; exact Nat.zero_lt_one }

private abbrev PrefixRaw {A : RankedSet} (root : Prop) (t b : A 1) (c : A 0) :=
  (v : (closedTest root (atomic t) (Lax369799.FiniteBranchWords.application b c)).Vertex) ×
    (Inner (closedTest root (atomic t) (Lax369799.FiniteBranchWords.application b c)).graph v).Vertex

private def prefixEquiv {A : RankedSet} (root : Prop) (t b : A 1) (c : A 0) :
    PrefixRaw root t b c ≃ Fin 3 where
  toFun := fun v => Fin.cases (fun w => Fin.cases 0 (fun _ => 2) w) (fun _ _ => 1) v.1 v.2
  invFun := Fin.cases ⟨(0 : Fin 2), (0 : Fin 2)⟩
    (Fin.cases ⟨(1 : Fin 2), (0 : Fin 1)⟩ (fun _ => ⟨(0 : Fin 2), (1 : Fin 2)⟩))
  left_inv := by rintro ⟨v, w⟩; fin_cases v <;> fin_cases w <;> rfl
  right_inv := by intro v; fin_cases v <;> rfl

private def prefixIso {A : RankedSet} (root : Prop) (t b : A 1) (c : A 0) :
    PresentationIso (flattenPresentation
      (closedTest root (atomic t) (Lax369799.FiniteBranchWords.application b c)).graph)
      (test root t b c).graph where
  vertex := prefixEquiv root t b c
  label := by rintro ⟨v, w⟩; fin_cases v <;> fin_cases w <;> rfl
  initial := by rintro ⟨v, w⟩; exact ⟨False.elim, fun h => h.1⟩
  root := by
    rintro ⟨v, w⟩
    fin_cases v <;> fin_cases w
    · change ((0 : Fin 3) = 1 ∨ (0 = 0 ∧ root)) ↔
        (False ∨ (((0 : Fin 2) = 1 ∨ (0 = 0 ∧ root)) ∧ (0 : Fin 2) = 0))
      simp
    · change ((2 : Fin 3) = 1 ∨ (2 = 0 ∧ root)) ↔
        (False ∨ (((0 : Fin 2) = 1 ∨ (0 = 0 ∧ root)) ∧ (1 : Fin 2) = 0))
      simp [show (2 : Fin 3) ≠ 0 by decide, show (2 : Fin 3) ≠ 1 by decide]
    · change ((1 : Fin 3) = 1 ∨ (1 = 0 ∧ root)) ↔
        (False ∨ (((1 : Fin 2) = 1 ∨ (1 = 0 ∧ root)) ∧ True))
      simp
  edge := by
    rintro ⟨v, w⟩ d s
    rcases s with ⟨q, u⟩ | j
    · fin_cases v <;> fin_cases w <;> fin_cases q <;> fin_cases u
      all_goals
        dsimp +instances [prefixEquiv, closedTest, Lax369799.FiniteBranchWords.application,
          test, flattenPresentation, Inner, atomic, ofSetSystem, Lax369799.RankedSystems.atomic,
          Fin.cases, Fin.induction, Fin.induction.go]
        simp <;> simp [Fin.induction.go]
      · exact fun _ => rfl
      · exact fun _ => (by decide : (1 : Fin 2) ≠ 0)
    · exact Fin.elim0 j

private theorem test_application {A : RankedSet} (E : Algebra A)
    (root : Prop) (t b : A 1) (c : A 0) :
    E.eval 0 (test root t b c) =
      E.eval 0 (closedTest root t (Lax369799.FiniteBranchWords.act E b c)) := by
  have hi : Isomorphic
      (flatten (closedTest root (atomic t) (Lax369799.FiniteBranchWords.application b c)))
      (test root t b c) :=
    ⟨UntrimmedFlattening.isoTrans
      (UntrimmedFlattening.isoSymm (UntrimmedFlattening.reindexIso _ (Fintype.equivFin _)))
      (prefixIso root t b c)⟩
  have he : relabel E.eval (closedTest root (atomic t) (Lax369799.FiniteBranchWords.application b c)) =
      closedTest root t (Lax369799.FiniteBranchWords.act E b c) := by
    dsimp only [relabel, closedTest]
    congr 1
    congr 1
    funext v
    fin_cases v
    · rfl
    · exact congrArg (Sigma.mk 1) (E.unit 1 t)
  exact (E.isomorphic _ _ _ hi).symm.trans
    ((E.associative _ _).symm.trans (congrArg (E.eval 0) he))

private theorem closed_normal_form {A : RankedSet} (E : Algebra A)
    (root : Prop) (t : A 1) (c : A 0) :
    E.eval 0 (Lax369799.FiniteContexts.plug
      (Lax369799.FiniteNormalForms.normalContext ⟨root, ∅⟩ (fun _ => t)) (atomic c)) =
      E.eval 0 (closedTest root t c) := by
  unfold Lax369799.FiniteContexts.plug
  rw [← E.associative]
  apply congrArg (E.eval 0)
  dsimp only [Lax369799.FiniteNormalForms.normalContext,
    Lax369799.ExtremalContexts.normalContext, Lax369799.ExtremalContexts.normalSystem,
    ofSetSystem, relabel, closedTest]
  congr 1
  congr 1
  · funext v
    fin_cases v
    · exact congrArg (Sigma.mk 0) (E.unit 0 c)
    · exact congrArg (Sigma.mk 1) (E.unit 1 t)
  · funext v d s
    fin_cases v
    · simp [Lax369799.ExtremalContexts.normalPresentation]
    · apply propext
      change (d = 0 ∧ s = .inl 0) ↔ ((1 : Fin 2) = 1 ∧ d = 0 ∧ s = .inl 0)
      simp

open Lax369799.FiniteContexts Lax369799.FiniteNormalForms
open Lax369799.ExpandedSyntacticAlgebra
open Lax369799.FiniteBranchWords

private theorem normalize_test {A : RankedSet} (L : Lax369799.Algebras.Language A)
    (E : SyntacticAlgebra L) (C : Context (Carrier (Accepting L)) 0 0)
    (a : Carrier (Accepting L) 0) :
    AcceptingClass (Accepting L) (E.algebra.eval 0 (plug C (atomic a))) ↔
      AcceptingClass (Accepting L) (E.algebra.eval 0
        (closedTest (plantedBoundary C).root (pieceValue E.algebra C 0) a)) := by
  have hc := fun n (S T : FiniteSystem (Carrier (Accepting L)) n) f hf =>
    FiniteOuterMorphisms.evaluation_cover L E.algebra E.evaluates (S := S) (T := T) f hf
  have hb : plantedBoundary C = ⟨(plantedBoundary C).root, ∅⟩ := by
    generalize plantedBoundary C = B
    obtain ⟨r, l⟩ := B
    congr 1
    apply Set.ext
    intro i
    exact Fin.elim0 i
  have hm : pieceValue E.algebra C = fun _ => pieceValue E.algebra C 0 := by
    funext i
    fin_cases i
    rfl
  have h := FiniteNormalForms.algebraic_decomposition E.algebra hc C a
  rw [hb, hm, closed_normal_form] at h
  rw [h]
  exact (FinitePlant.accepting_evaluation_plant L E.algebra E.evaluates _).symm

private theorem context_monotone {A : RankedSet} (L : Lax369799.Algebras.Language A)
    (E : SyntacticAlgebra L) {k n : ℕ} (C : Context (Carrier (Accepting L)) k n)
    (a b : Carrier (Accepting L) k) (hab : ClassBelow (Accepting L) a b) :
    ClassBelow (Accepting L) (E.algebra.eval n (plug C (atomic a)))
      (E.algebra.eval n (plug C (atomic b))) := by
  rw [E.algebra.isomorphic _ _ _ (FiniteNormalForms.plug_atomic_iso C a),
    E.algebra.isomorphic _ _ _ (FiniteNormalForms.plug_atomic_iso C b)]
  apply FiniteSyntacticAlgebra.evaluation_monotone (Accepting L)
    (FiniteAcceptance.accepting_isomorphic L) E.algebra E.evaluates C.system
    (fun v => FiniteNormalForms.letterSubstitution a _ (C.system.graph.label v).2)
    (fun v => FiniteNormalForms.letterSubstitution b _ (C.system.graph.label v).2)
  intro v
  generalize C.system.graph.label v = l
  obtain ⟨r, l⟩ := l
  cases l with
  | inl l => exact (FiniteContextualOrder.class_order (Accepting L) r).1 _
  | inr h => obtain ⟨h⟩ := h; subst r; exact hab

private theorem act_monotone {A : RankedSet} (L : Lax369799.Algebras.Language A)
    (E : SyntacticAlgebra L) (b : Carrier (Accepting L) 1)
    (c d : Carrier (Accepting L) 0) (hcd : ClassBelow (Accepting L) c d) :
    ClassBelow (Accepting L) (act E.algebra b c) (act E.algebra b d) := by
  let P := application b c
  let q : ∀ v : P.Vertex, Carrier (Accepting L) (P.graph.label v).1 :=
    Fin.cases b (fun _ => c)
  let r : ∀ v : P.Vertex, Carrier (Accepting L) (P.graph.label v).1 :=
    Fin.cases b (fun _ => d)
  have hq : withLabels P q = application b c := by
    dsimp [withLabels, P, application, q]; congr 1; congr 1; funext v; fin_cases v <;> rfl
  have hr : withLabels P r = application b d := by
    dsimp [withLabels, P, application, r]; congr 1; congr 1; funext v; fin_cases v <;> rfl
  have hh := FiniteSyntacticAlgebra.evaluation_monotone (Accepting L)
    (FiniteAcceptance.accepting_isomorphic L) E.algebra E.evaluates P q r (by
      intro v; fin_cases v
      · exact (FiniteContextualOrder.class_order (Accepting L) 1).1 _
      · exact hcd)
  rwa [hq, hr] at hh

private theorem selected_test_sum {A : RankedSet} (L : Lax369799.Algebras.Language A)
    (E : SyntacticAlgebra L) (b : Carrier (Accepting L) 1)
    (hb : Lax369799.ExtremalUnaryTypes.Selected L E b)
    (root : Prop) (t : Carrier (Accepting L) 1) (c d : Carrier (Accepting L) 0) :
    AcceptingClass (Accepting L) (E.algebra.eval 0
        (closedTest root t (act E.algebra b (sumValue E.algebra c d)))) ↔
      AcceptingClass (Accepting L) (E.algebra.eval 0 (closedTest root t (act E.algebra b c))) ∧
      AcceptingClass (Accepting L) (E.algebra.eval 0 (closedTest root t (act E.algebra b d))) := by
  obtain ⟨a, x, hx, rfl⟩ := hb
  have h := SplitExtremal.accepting_meetData L E.algebra E.evaluates (by omega) x
    (data E.algebra root t c) (data E.algebra root t d) a hx
  rw [← UnaryTestContexts.data_sum L E.algebra E.evaluates] at h
  unfold Lax369799.FiniteExtremal.Accepts at h
  simp only [normal_form L E.algebra E.evaluates, test_application] at h
  exact h

/--
---
conclusion: Lax369799.SelectedChoicePreservation.selected_preserves_choices
---
Normalize an arbitrary closed testing context. Extremality turns the
meet of continuation data into conjunction. Monotonicity supplies one
inequality; separation by all contexts supplies the converse.
-/
theorem selected_preserves_choices {A : RankedSet} (L : Lax369799.Algebras.Language A)
    (E : SyntacticAlgebra L) (b : Carrier (Accepting L) 1)
    (hb : Lax369799.ExtremalUnaryTypes.Selected L E b) :
    Lax369799.ChoicePreservingUnary.PreservesChoices E.algebra b := by
  intro c d
  let F := Accepting L
  have ho := FiniteContextualOrder.class_order F 0
  have hm (u v : Carrier F 0) :
      ClassBelow F (sumValue E.algebra u v) u ∧ ClassBelow F (sumValue E.algebra u v) v :=
    (FiniteOrderedAlgebra.sum_value_meet L E.algebra E.evaluates _ _ _).mp (ho.1 _)
  apply ho.2.1
  · apply (FiniteOrderedAlgebra.sum_value_meet L E.algebra E.evaluates _ _ _).mpr
    exact ⟨act_monotone L E b _ _ (hm c d).1, act_monotone L E b _ _ (hm c d).2⟩
  · apply FiniteEvaluation.order_separating F (FiniteAcceptance.accepting_isomorphic L)
      E.algebra E.evaluates
    intro C hC
    have hup := (FiniteSyntacticAlgebra.accepting_classes F (FiniteAcceptance.accepting_isomorphic L)).2
    have hc := hup _ _ hC (context_monotone L E C _ _ (hm (act E.algebra b c) (act E.algebra b d)).1)
    have hd := hup _ _ hC (context_monotone L E C _ _ (hm (act E.algebra b c) (act E.algebra b d)).2)
    apply (normalize_test L E C _).mpr
    exact (selected_test_sum L E b hb _ _ c d).mpr
      ⟨(normalize_test L E C _).mp hc, (normalize_test L E C _).mp hd⟩

end Lax369799Proofs.SelectedChoicePreservation
