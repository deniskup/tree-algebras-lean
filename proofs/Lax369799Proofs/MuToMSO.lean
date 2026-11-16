import Lax369799.MuCalculusTheorems
import Lax369799Proofs.UnrestrictedLogic

namespace Lax369799Proofs.MuToMSO
set_option backward.isDefEq.respectTransparency false
open Lax369799 TransitionSystems

/--
---
conclusion: Lax369799.MuCalculusTheorems.mu_to_mso
---
Specialize the translation on arbitrary state spaces to a finite
presentation, using agreement of the two semantic interpretations.
-/
theorem mu_to_mso {P : Type} (φ : ModalMuCalculus.Sentence P) :
    ∃ ψ : MonadicSecondOrder.Sentence P, ∀ S,
      ModalMuCalculus.Models S φ ↔ MonadicSecondOrder.Models S ψ := by
  obtain ⟨ψ,hψ⟩ := UnrestrictedLogic.mu_to_mso φ
  refine ⟨ψ,fun S => ?_⟩
  exact (UnrestrictedLogic.finite_mu_models S φ).symm.trans
    ((hψ (UnrestrictedTransitionSystems.ofFinite S)).trans (UnrestrictedLogic.finite_mso_models S ψ))

end Lax369799Proofs.MuToMSO
