import Lax369799.FiniteBranchWords
import Lax369799.UnfoldAutomata
import Mathlib.Data.Fintype.Prod

/-!
---
title: Combining finite and infinite branch conditions
type: theorem
---
The finite-word evaluator can be combined with any parity condition on
infinite words. The product reads both components in parallel, uses the
parity component's priorities, and tests the evaluator's final state on
terminating words.
-/
namespace Lax369799.CombinedWordCondition
open UnfoldAutomata FiniteBranchWords

noncomputable def combine {u z : ℕ} (D : WordCondition u z)
    (f : Fin u → Fin z → Fin z) (F : Set (Fin z)) : WordCondition u z := by
  classical
  let Q := Fin D.states × State (Fin z)
  let e := Fintype.equivFin Q
  exact {
    states := Fintype.card Q
    initial := e (D.initial, (machine f F).start)
    step := fun q a => e (D.step (e.symm q).1 a, (machine f F).step (e.symm q).2 a)
    priority := fun q => D.priority (e.symm q).1
    final := {q | (e.symm q).2 ∈ (machine f F).accept} }

axiom finite_iff {u z : ℕ} (D : WordCondition u z)
    (f : Fin u → Fin z → Fin z) (F : Set (Fin z))
    (w : List (Fin u)) (a : Fin z) :
    (combine D f F).AcceptsFinite w a ↔ w.foldr f a ∈ F

axiom infinite_iff {u z : ℕ} (D : WordCondition u z)
    (f : Fin u → Fin z → Fin z) (F : Set (Fin z))
    (w : ℕ → Fin u) :
    (combine D f F).AcceptsInfinite w ↔ D.AcceptsInfinite w

end Lax369799.CombinedWordCondition
