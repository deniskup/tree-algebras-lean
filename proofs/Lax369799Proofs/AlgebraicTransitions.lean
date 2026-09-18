import Lax369799.AlgebraicTransitions
import Lax369799Proofs.DeterministicElements

namespace Lax369799Proofs.AlgebraicTransitions
open Lax369799.RankedSystems Lax369799.SetAlgebras Lax369799.AutomatonProperty
open Lax369799.UnfoldAutomata Lax369799.AlgebraicTransitions Lax369799.Flattening

/--
---
conclusion: Lax369799.AlgebraicTransitions.accepting_transition
---
Choose the deterministic witness supplied by the automaton property.
Express it as a parallel family of unary values and enumerate these
values as finite edge types. The original inequalities give transition
membership and acceptance preservation.
-/
theorem accepting_transition {A B : RankedSet} [Fintype (B 1)] [Fintype (B 0)]
    (E : SetAlgebra B) (f : B 0) (hE : HasAutomatonProperty E f) (η : RankedMap A B)
    (D : WordCondition (Fintype.card (B 1)) (Fintype.card (B 0)))
    (n : ℕ) (a : A (n + 1)) (C : SetContext B (n + 1) 0)
    (h : Below E f (E.eval 0 (plug C (atomic (η (n + 1) a))))) :
    ∃ b ∈ (automaton E η D).transition n a,
      Below E f (E.eval 0 (plug C
        (atomic (E.eval (n + 1) (Lax369799.DeterministicElements.parallel (decodeTypes b)))))) := by
  obtain ⟨δ, hδ, hbelow, hacc⟩ := hE (n + 1) C (η (n + 1) a) h
  obtain ⟨b, hb⟩ := (DeterministicElements.unary_normal_form E (Nat.succ_pos n) δ).mp hδ
  let t := fun i => (Fintype.equivFin (B 1)) (b i)
  have ht : decodeTypes t = b := by
    funext i
    exact (Fintype.equivFin (B 1)).symm_apply_apply (b i)
  refine ⟨t, ?_, ?_⟩
  · change Below E (E.eval (n + 1) (Lax369799.DeterministicElements.parallel (decodeTypes t))) _
    rw [ht, hb]
    exact hbelow
  · rw [ht, hb]
    exact hacc

end Lax369799Proofs.AlgebraicTransitions
