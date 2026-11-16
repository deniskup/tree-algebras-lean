import Lax369799.MuCalculusTheorems
import Lax369799Proofs.UnrestrictedLogic

namespace Lax369799Proofs.MuBisimulation
set_option backward.isDefEq.respectTransparency false
open Lax369799 TransitionSystems ModalMuCalculus

/--
---
conclusion: Lax369799.MuCalculusTheorems.mu_bisimulation_invariant
---
Bisimulation invariance on arbitrary state spaces specializes to finite
presentations. The semantic comparison preserves the initial-state test.
-/
theorem mu_bisimulation_invariant {P : Type} (φ : Sentence P) :
    BisimulationInvariant {S | Models S φ} := by
  intro S T hST
  obtain ⟨R,hR⟩ := hST
  have h : UnrestrictedTransitionSystems.Bisimilar
      (UnrestrictedTransitionSystems.ofFinite S) (UnrestrictedTransitionSystems.ofFinite T) := ⟨R,hR⟩
  have he := UnrestrictedLogic.mu_bisimulation_invariant φ _ _ h
  exact (UnrestrictedLogic.finite_mu_models S φ).symm.trans
    (he.trans (UnrestrictedLogic.finite_mu_models T φ))

end Lax369799Proofs.MuBisimulation
