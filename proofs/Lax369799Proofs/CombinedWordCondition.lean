import Lax369799.CombinedWordCondition
import Lax369799Proofs.FiniteBranchWords

namespace Lax369799Proofs.CombinedWordCondition
set_option backward.isDefEq.respectTransparency false
open Lax369799.UnfoldAutomata Lax369799.FiniteBranchWords Lax369799.CombinedWordCondition

private theorem second_fold {u z : ℕ} (D : WordCondition u z)
    (f : Fin u → Fin z → Fin z) (F : Set (Fin z))
    (w : List (Fin u)) (q : Fin (combine D f F).states) :
    ((Fintype.equivFin (Fin D.states × State (Fin z))).symm
      (w.foldl (fun q b => (combine D f F).step q (.inl b)) q)).2 =
    (machine f F).evalFrom
      ((Fintype.equivFin (Fin D.states × State (Fin z))).symm q).2 (w.map Sum.inl) := by
  classical
  induction w generalizing q with
  | nil => rfl
  | cons b w ih =>
    rw [List.foldl_cons, List.map_cons, DFA.evalFrom_cons, ih]
    congr 1
    simp only [combine, Equiv.symm_apply_apply]

/--
---
conclusion: Lax369799.CombinedWordCondition.finite_iff
---
The second component tracks the unary action and applies it to the
terminal nullary type; the first component does not affect finality.
-/
theorem finite_iff {u z : ℕ} (D : WordCondition u z)
    (f : Fin u → Fin z → Fin z) (F : Set (Fin z))
    (w : List (Fin u)) (a : Fin z) :
    (combine D f F).AcceptsFinite w a ↔ w.foldr f a ∈ F := by
  classical
  let e := Fintype.equivFin (Fin D.states × State (Fin z))
  change (e.symm ((combine D f F).step
    (w.foldl (fun q b => (combine D f F).step q (.inl b)) (combine D f F).initial)
      (.inr a))).2 ∈ (machine f F).accept ↔ _
  have hs (q : Fin (combine D f F).states) (c : Fin u ⊕ Fin z) :
      (e.symm ((combine D f F).step q c)).2 = (machine f F).step (e.symm q).2 c := by
    simp only [combine, e, Equiv.symm_apply_apply]
  rw [hs]
  dsimp only [e]
  erw [second_fold D f F w (combine D f F).initial]
  simp only [combine, Equiv.symm_apply_apply]
  change (machine f F).step ((machine f F).eval (w.map Sum.inl)) (.inr a) ∈ _ ↔ _
  rw [← DFA.eval_append_singleton, FiniteBranchWords.evaluate]
  change (∃ b ∈ F, some (Sum.inr (w.foldr f a)) = some (Sum.inr b)) ↔ _
  simp

private theorem first_run {u z : ℕ} (D : WordCondition u z)
    (f : Fin u → Fin z → Fin z) (F : Set (Fin z)) (w : ℕ → Fin u) (n : ℕ) :
    ((Fintype.equivFin (Fin D.states × State (Fin z))).symm
      ((combine D f F).run w n)).1 = D.run w n := by
  classical
  induction n with
  | zero => simp [WordCondition.run, combine]
  | succ n ih =>
    simpa only [WordCondition.run, combine, Equiv.symm_apply_apply] using
      (congrArg (fun q => D.step q (.inl (w n))) ih)

/--
---
conclusion: Lax369799.CombinedWordCondition.infinite_iff
---
The first projection follows the original run and supplies exactly the
same priority at every position.
-/
theorem infinite_iff {u z : ℕ} (D : WordCondition u z)
    (f : Fin u → Fin z → Fin z) (F : Set (Fin z)) (w : ℕ → Fin u) :
    (combine D f F).AcceptsInfinite w ↔ D.AcceptsInfinite w := by
  have hp (n : ℕ) : (combine D f F).priority ((combine D f F).run w n) =
      D.priority (D.run w n) := congrArg D.priority (first_run D f F w n)
  simp only [WordCondition.AcceptsInfinite, hp]

end Lax369799Proofs.CombinedWordCondition
