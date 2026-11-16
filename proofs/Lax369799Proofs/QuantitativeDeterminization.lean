import Lax369799.QuantitativeDeterminization
import Lax369799Proofs.OmegaDeterminization
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Pi
import Mathlib.Tactic.Ring

set_option backward.isDefEq.respectTransparency false
namespace Lax369799Proofs.QuantitativeDeterminization
open Lax369799
open UnfoldAutomata OmegaDeterminization
open Lax369799.QuantitativeDeterminization
open WordAutomata

private theorem position_card (Q : Type) [Fintype Q] :
    Nat.card (Safra.FPos Q) ≤ (Fintype.card Q+2)^(Fintype.card Q) := by
  let f : Safra.FPos Q → Fin (Fintype.card Q) → Option (Safra.Slot Q) :=
    fun p i => p.val[i.val]?
  have hf : Function.Injective f := by
    intro p q h
    apply Subtype.ext
    apply List.ext_getElem?
    intro i
    by_cases hi : i < Fintype.card Q
    · exact congrFun h ⟨i,hi⟩
    · have hp : p.val.length ≤ i := p.property.trans (Nat.le_of_not_gt hi)
      have hq : q.val.length ≤ i := q.property.trans (Nat.le_of_not_gt hi)
      simp only [List.getElem?_eq_none hp,List.getElem?_eq_none hq]
  have hc := Nat.card_le_card_of_injective f hf
  simpa [Nat.card_eq_fintype_card,Safra.Slot,Safra.numSlots] using hc

private theorem safra_card (Q : Type) [Fintype Q] :
    Nat.card (Safra.SafraState Q) ≤ safraBound (Fintype.card Q) := by
  classical
  let : Fintype (Safra.FPos Q) := Fintype.ofFinite _
  have he : Nat.card (Safra.SafraState Q) =
      (2^(Fintype.card Q+1))^(Nat.card (Safra.FPos Q)) := by
    simp [Safra.SafraState,Nat.card_eq_fintype_card,Nat.pow_succ]
  rw [he]
  exact Nat.pow_le_pow_right (Nat.pow_pos (by decide)) (position_card Q)

private theorem safra_mono : Monotone safraBound := by
  intro n m h
  unfold safraBound
  apply (Nat.pow_le_pow_left (Nat.pow_le_pow_right (by decide) (Nat.add_le_add_right h 1)) _).trans
  apply Nat.pow_le_pow_right (Nat.pow_pos (by decide))
  exact (Nat.pow_le_pow_left (Nat.add_le_add_right h 2) _).trans
    (Nat.pow_le_pow_right (by omega) h)

/--
---
conclusion: Lax369799.QuantitativeDeterminization.determinization_bound
---
A bounded Safra position is encoded by a padded vector of optional slots.
Labels and marks then bound the Muller state type explicitly. Appearance
records multiply this by the number of rankings, and the parity conversion
uses at most twice the Muller-state bound.
-/
theorem determinization_bound {u z : ℕ} (B : Buchi u) (bound : ℕ) (hb : B.states ≤ bound) :
    ∃ D : WordCondition u z,
      (∀ w,D.AcceptsInfinite w ↔ B.Accepts w) ∧
      D.states ≤ stateBound bound ∧ (∀ q,D.priority q ≤ priorityBound bound) := by
  classical
  let N : NBuchi (Fin B.states) (Fin u) := ⟨B.initial,B.transition,B.accepting⟩
  let S := Safra.SafraState (Fin B.states)
  let : Fintype S := Fintype.ofFinite S
  let M := Safra.detAut N
  let D : WordCondition u z := OmegaDeterminization.parity M
  have hs : Fintype.card S ≤ safraBound bound := by
    have hc : Fintype.card S ≤ safraBound B.states := by
      simpa only [Nat.card_eq_fintype_card,Fintype.card_fin] using safra_card (Fin B.states)
    exact hc.trans (safra_mono hb)
  have hpos : 1 ≤ safraBound bound := by
    unfold safraBound
    exact Nat.one_le_pow _ _ (Nat.pow_pos (by decide))
  refine ⟨D,?_,?_,?_⟩
  · intro w
    apply (OmegaDeterminization.parity_correct M w).trans
    have h := Safra.accepts_detAut_iff (B := N) (w := w)
    change M.Accepts w ↔ _ at h
    exact h.trans (by simp only [NBuchi.Accepts,NBuchi.IsRun,Buchi.Accepts,and_assoc];rfl)
  · change Fintype.card (S × (S → Fin (Fintype.card S))) ≤ stateBound bound
    simp only [Fintype.card_prod,Fintype.card_fun,Fintype.card_fin]
    exact Nat.mul_le_mul hs ((Nat.pow_le_pow_left hs _).trans (Nat.pow_le_pow_right hpos hs))
  · intro q
    exact (Nat.sub_le _ _).trans (Nat.mul_le_mul_left 2 hs)

end Lax369799Proofs.QuantitativeDeterminization
