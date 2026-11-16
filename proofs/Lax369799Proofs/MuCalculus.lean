import Lax369799.MuCalculusTheorems
import Lax369799Proofs.UnrestrictedLogic

namespace Lax369799Proofs.MuCalculus
set_option backward.isDefEq.respectTransparency false
open Lax369799 TransitionSystems ModalMuCalculus

/--
---
conclusion: Lax369799.MuCalculusTheorems.eval_monotone
---
Specialize monotonicity on arbitrary state spaces to finite presentations.
-/
theorem eval_monotone {P : Type} (S : TransitionSystem P) {n : ℕ}
    (φ : Formula P n) (ρ σ : Fin n → Set S.Vertex)
    (h : ∀ i, ρ i ⊆ σ i) : φ.eval S ρ ⊆ φ.eval S σ := by
  have he := UnrestrictedLogic.eval_monotone (UnrestrictedTransitionSystems.ofFinite S) φ ρ σ h
  rw [UnrestrictedLogic.finite_mu,UnrestrictedLogic.finite_mu] at he
  exact he

end Lax369799Proofs.MuCalculus
