import Lax369799.MuCalculusTheorems

namespace Lax369799Proofs.MuCalculus
open Lax369799.TransitionSystems Lax369799.ModalMuCalculus

/--
---
conclusion: Lax369799.MuCalculusTheorems.eval_monotone
---
Induct on formulas. Increasing an environment decreases the set of
pre-fixed points and increases the set of post-fixed points.
-/
theorem eval_monotone {P : Type} (S : TransitionSystem P) {n : ℕ}
    (φ : Formula P n) (ρ σ : Fin n → Set S.Vertex)
    (h : ∀ i, ρ i ⊆ σ i) : φ.eval S ρ ⊆ φ.eval S σ := by
  induction φ with
  | top => exact Set.Subset.rfl
  | bot => exact Set.Subset.rfl
  | proposition p => exact Set.Subset.rfl
  | negProposition p => exact Set.Subset.rfl
  | «variable» i => exact h i
  | conj φ ψ ihφ ihψ => exact Set.inter_subset_inter (ihφ ρ σ h) (ihψ ρ σ h)
  | disj φ ψ ihφ ihψ => exact Set.union_subset_union (ihφ ρ σ h) (ihψ ρ σ h)
  | diamond φ ih =>
    rintro v ⟨w, he, hw⟩
    exact ⟨w, he, ih ρ σ h hw⟩
  | box φ ih =>
    intro v hv w he
    exact ih ρ σ h (hv w he)
  | mu φ ih =>
    apply le_sInf
    intro X hX
    apply sInf_le
    exact (ih (Fin.cases X ρ) (Fin.cases X σ) (by intro i; refine Fin.cases ?_ ?_ i; exact Set.Subset.rfl; exact h)).trans hX
  | nu φ ih =>
    apply sSup_le
    intro X hX
    apply le_sSup
    exact hX.trans (ih (Fin.cases X ρ) (Fin.cases X σ) (by intro i; refine Fin.cases ?_ ?_ i; exact Set.Subset.rfl; exact h))

end Lax369799Proofs.MuCalculus
