import Lax369799.QuantitativeFiniteTheorem
import Lax369799Proofs.QuantitativeAutomata
import Lax369799Proofs.QuantitativeRecognition
import Lax369799Proofs.ModalSmallModels
import Lax369799Proofs.BisimAutomatonTheorem
import Lax369799Proofs.Encoding
import Lax369799Proofs.RankedBisimulation

set_option backward.isDefEq.respectTransparency false
namespace Lax369799Proofs.QuantitativeFiniteTheorem
open Lax369799
open RankedSystems Algebras TransitionEncoding TransitionSystems UnfoldAutomata
open ParityWinningRegions
open Lax369799.QuantitativeFiniteTheorem

private theorem accepts_winning {P : Type} [Finite P]
    (M : UnfoldAutomaton (TransitionAlphabet P)) (hM : BisimAutomata.IsBisimAutomaton M)
    (hL : ∀ S T,RankedBisimilar S T → (Accepts M S ↔ Accepts M T))
    (S : System (TransitionAlphabet P) 0) :
    Accepts M S ↔ Winning (ModalAcceptanceGame.game M (decode S)) true
      (ModalAcceptanceGame.position M.condition.initial (decode S).initial) := by
  classical
  let : Fintype P := Fintype.ofFinite P
  let ψ := ModalGameTranslation.sentence M M.condition.initial
  constructor
  · rintro ⟨T,hST,r,hr⟩
    have hT : ModalMuCalculus.Models (decode T) ψ :=
      (ModalGameTranslation.sentence_correct M (decode T) _ _).mpr (AutomatonRunGame.run_winning M r hr)
    have hb := RankedBisimulation.ranked_forward S T (Relation.EqvGen.rel _ _ (Or.inl hST))
    have hS := (MuBisimulation.mu_bisimulation_invariant ψ (decode S) (decode T) hb).mpr hT
    exact (ModalGameTranslation.sentence_correct M (decode S) _ _).mp hS
  · intro hS
    obtain ⟨U,hUS,r,hr⟩ := CloneGameRun.winning_run M hM (decode S) hS
    apply (hL U S ((EncodingBisimulation.bisimulation_iff U S).mpr hUS)).mp
    exact ⟨U,(MorphismTheorems.unfold_equivalence _ _).refl U.val,r,hr⟩

/--
---
conclusion: Lax369799.QuantitativeFiniteTheorem.modal_certificate
---
Apply quantitative recognition and clone normalization, retaining every
finite bound. The encoding and bisimulation theorems identify the modal
game with the original MSO sentence on every finite reachable system.
-/
theorem modal_certificate {P : Type} [Finite P] (φ : MonadicSecondOrder.Sentence P)
    (hφ : BisimulationInvariant {S | MonadicSecondOrder.Models S φ}) :
    ∃ M : UnfoldAutomaton (TransitionAlphabet P),
      M.unary ≤ QuantitativeAutomata.unaryBound (QuantitativeRecognition.msoBound φ) ∧
      M.nullary ≤ QuantitativeAutomata.nullaryBound (QuantitativeRecognition.msoBound φ) ∧
      M.condition.states ≤ modelBound φ ∧
      (∀ q,M.condition.priority q ≤ QuantitativeAutomata.priorityBound (QuantitativeRecognition.msoBound φ)) ∧
      ∀ S,MonadicSecondOrder.Models S φ ↔ Winning (ModalAcceptanceGame.game M S) true
        (ModalAcceptanceGame.position M.condition.initial S.initial) := by
  let L : Language (TransitionAlphabet P) := {S | MonadicSecondOrder.Models (decode S) φ}
  have hL : ∀ S T,RankedBisimilar S T → (S ∈ L ↔ T ∈ L) :=
    fun S T h => hφ (decode S) (decode T) (RankedBisimulation.ranked_forward S T h)
  obtain ⟨M,hM,hrec,hu,hz,hs,hp⟩ := QuantitativeAutomata.automaton_bound L hL
    (QuantitativeRecognition.msoBound φ) (QuantitativeRecognition.mso_bound φ)
  have hML : ∀ S T,RankedBisimilar S T → (Accepts M S ↔ Accepts M T) := by
    intro S T h
    exact (hrec S).symm.trans ((hL S T h).trans (hrec T))
  refine ⟨M,hu,hz,hs,hp,?_⟩
  intro S
  obtain ⟨T,rfl⟩ := Encoding.encoding_exists S
  exact (hrec T).trans (accepts_winning M hM hML T)

/--
---
conclusion: Lax369799.QuantitativeFiniteTheorem.nonempty_bound
---
The bounded modal certificate and the word-state small-model theorem
supply a model within the syntax-computed bound whenever the invariant
MSO sentence has a finite reachable model.
-/
theorem nonempty_bound {P : Type} [Finite P] (φ : MonadicSecondOrder.Sentence P)
    (hφ : BisimulationInvariant {S | MonadicSecondOrder.Models S φ})
    (h : ∃ S,MonadicSecondOrder.Models S φ) :
    ∃ T : TransitionSystem P,T.size ≤ modelBound φ ∧ MonadicSecondOrder.Models T φ := by
  obtain ⟨M,_,_,hs,_,he⟩ := modal_certificate φ hφ
  obtain ⟨S,hS⟩ := h
  obtain ⟨T,ht,hw⟩ := ModalSmallModels.small_model M S ((he S).mp hS)
  exact ⟨T,ht.trans hs,(he T).mpr hw⟩

end Lax369799Proofs.QuantitativeFiniteTheorem
