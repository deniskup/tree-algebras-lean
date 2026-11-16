import Lax369799.FiniteRecurrence

namespace Lax369799Proofs.FiniteRecurrence
open Lax369799.FiniteRecurrence

/--
---
conclusion: Lax369799.FiniteRecurrence.eventual_subset
---
Each element outside the recurrent set has a last-occurrence bound. Take
the maximum of these finitely many bounds.
-/
theorem eventual_subset {X : Type} [Finite X] (F : ℕ → Set X) :
    ∃ N, ∀ k, N ≤ k → F k ⊆ Recurrent F := by
  classical
  letI : Fintype X := Fintype.ofFinite X
  have h (x : X) : ∃ N, x ∉ Recurrent F → ∀ k, N ≤ k → x ∉ F k := by
    by_cases hx : x ∈ Recurrent F
    · exact ⟨0, fun h => (h hx).elim⟩
    · change ¬ ∀ N, ∃ k, N ≤ k ∧ x ∈ F k at hx
      push_neg at hx
      obtain ⟨N, hN⟩ := hx
      exact ⟨N, fun _ => hN⟩
  choose bound hbound using h
  refine ⟨Finset.univ.sup bound, fun k hk x hx => ?_⟩
  by_contra hn
  exact hbound x hn k ((Finset.le_sup (Finset.mem_univ x)).trans hk) hx

/--
---
conclusion: Lax369799.FiniteRecurrence.simultaneous
---
Take the maximum of the thresholds for the finitely many sequences.
-/
theorem simultaneous {I X : Type} [Finite I] [Finite X] (F : I → ℕ → Set X) :
    ∃ N, ∀ i k, N ≤ k → F i k ⊆ Recurrent (F i) := by
  classical
  letI : Fintype I := Fintype.ofFinite I
  choose bound hbound using fun i => eventual_subset (F i)
  exact ⟨Finset.univ.sup bound, fun i k hk => hbound i k
    ((Finset.le_sup (Finset.mem_univ i)).trans hk)⟩

end Lax369799Proofs.FiniteRecurrence
