import Lax369799.BisimAutomatonTheorem
import Lax369799Proofs.AutomatonRunGame
import Lax369799Proofs.CloneGameRun
import Lax369799Proofs.ModalGameTranslation
import Lax369799Proofs.EncodingBisimulation
import Lax369799Proofs.MuBisimulation

namespace Lax369799Proofs.BisimAutomatonTheorem
open Lax369799
open RankedSystems Algebras UnfoldAutomata TransitionEncoding BisimAutomata

/--
---
conclusion: Lax369799.BisimAutomatonTheorem.bisim_automaton_to_mu
---
The modal game has a sentence defining its winning region. Accepting runs
give winning plays, and sentence invariance transfers this across an
unfolding. Conversely, a winning strategy yields a bisimilar finite
presentation with an accepting run; the assumed language invariance
transfers acceptance back to the input presentation.
-/
theorem bisim_automaton_to_mu {P : Type} [Finite P]
    (M : UnfoldAutomaton (TransitionAlphabet P)) (hM : IsBisimAutomaton M)
    (hL : ∀ S T, RankedBisimilar S T → (Accepts M S ↔ Accepts M T)) :
    ∃ φ : ModalMuCalculus.Sentence P, ∀ S,
      Accepts M S ↔ ModalMuCalculus.Models (decode S) φ := by
  obtain ⟨φ, hφ⟩ := ModalGameTranslation.game_to_mu M
  refine ⟨φ, fun S => ⟨?_, ?_⟩⟩
  · rintro ⟨T, hST, r, hr⟩
    have hT := (hφ (decode T)).mp (AutomatonRunGame.run_winning M r hr)
    have hb := RankedBisimulation.ranked_forward S T (Relation.EqvGen.rel _ _ (Or.inl hST))
    exact (MuBisimulation.mu_bisimulation_invariant φ (decode S) (decode T) hb).mpr hT
  · intro hS
    obtain ⟨U, hUS, r, hr⟩ := CloneGameRun.winning_run M hM (decode S) ((hφ _).mpr hS)
    apply (hL U S ((EncodingBisimulation.bisimulation_iff U S).mpr hUS)).mp
    exact ⟨U, (MorphismTheorems.unfold_equivalence (TransitionAlphabet P) 0).refl U.val, r, hr⟩

end Lax369799Proofs.BisimAutomatonTheorem
