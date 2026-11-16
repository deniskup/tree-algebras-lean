import Lax369799.CloneTransitions
import Lax369799.BranchMonotonicity

/-!
---
title: Refining runs of the clone table
type: theorem
---
An accepting run of the recurrent clone table lifts to an accepting run
of the original transition table on a system with isomorphic decoding.
The direction map is surjective, labels increase along every branch,
and the algebraic word condition is monotone.
-/
namespace Lax369799.CloneRunRefinement
open RankedSystems (RankedSet System)
open TransitionEncoding UnfoldAutomata SetSystemAlgebras

noncomputable def fromTable {P : Type} {Y : RankedSet} [Fintype (Y 1)] [Fintype (Y 0)]
    (T : Set P → ∀ n, Set (Fin (n + 1) → Y 1))
    (leaves : Set P → Set (Fin (Fintype.card (Y 0))))
    (D : WordCondition (Fintype.card (Y 1)) (Fintype.card (Y 0))) :
    UnfoldAutomaton (TransitionAlphabet P) where
  unary := Fintype.card (Y 1)
  nullary := Fintype.card (Y 0)
  transition := fun n ν => {b | (fun i => (Fintype.equivFin (Y 1)).symm (b i)) ∈ T ν n}
  leafTransition := leaves
  condition := D

variable {P : Type} {Y : RankedSet} (E : SetAlgebra Y)
    [Fintype (Y 1)] [Fintype (Y 0)]
    (T : Set P → ∀ n, Set (Fin (n + 1) → Y 1))
    (leaves : Set P → Set (Fin (Fintype.card (Y 0))))
    (D : WordCondition (Fintype.card (Y 1)) (Fintype.card (Y 0)))
    (S : System (TransitionAlphabet P) 0)
    (r : Run (CloneTransitions.automaton (CloneTransitions.beta E T) leaves D) S)

axiom run_refinement
    (hD : Lax369799.BranchMonotonicity.ConditionMonotone E D) (hr : r.Accepting) :
    ∃ U : System (TransitionAlphabet P) 0, Isomorphic (decode U) (decode S) ∧
      ∃ s : Run (fromTable T leaves D) U, s.Accepting

end Lax369799.CloneRunRefinement
