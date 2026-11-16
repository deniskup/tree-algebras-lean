import Lax369799Proofs.EffectiveFiniteTranslation
import Lax369799Proofs.CloneNormalization
import Lax369799.FiniteBisimulationTheorem
import Lax369799Proofs.MSORecognition
import Lax369799.EncodingTheorems
import Lax369799.MuCalculusTheorems
import Lax369799.AlgebraToMuCalculus
import Lax369799.BisimAutomatonTheorem
import Lax369799Proofs.Encoding
import Lax369799Proofs.RankedBisimulation
import Lax369799Proofs.MuToMSO
import Lax369799Proofs.MuBisimulation
import Lax369799Proofs.BisimAutomatonTheorem

namespace Lax369799Proofs.MainTheorems
open Lax369799
open RankedSystems Algebras TransitionEncoding TransitionSystems

/--
---
conclusion: Lax369799.AlgebraToMuCalculus.algebra_to_mu
---
Use the proved clone normalization, then apply its modal translation.
-/
theorem algebra_to_mu {P : Type} [Finite P] (L : Language (TransitionAlphabet P))
    (hL : ∀ S T, RankedBisimilar S T → (S ∈ L ↔ T ∈ L))
    (hA : SupportedAlgebras.Recognizable L) :
    ∃ φ : ModalMuCalculus.Sentence P, ∀ S, S ∈ L ↔ ModalMuCalculus.Models (decode S) φ := by
  obtain ⟨M, hM, hrec⟩ := CloneNormalization.bisim_automaton_exists L hL hA
  have hinv : ∀ S T, RankedBisimilar S T → (UnfoldAutomata.Accepts M S ↔ UnfoldAutomata.Accepts M T) := by
    intro S T h
    exact (hrec S).symm.trans ((hL S T h).trans (hrec T))
  obtain ⟨φ, hφ⟩ := BisimAutomatonTheorem.bisim_automaton_to_mu M hM hinv
  exact ⟨φ, fun S => (hrec S).trans (hφ S)⟩

/--
---
conclusion: Lax369799.FiniteBisimulationTheorem.finite_bisimulation_invariant_mso
---
Encode finite transition systems as ranked systems, apply MSO recognition
and the algebraic modal translation, and decode. The converse combines
the standard MSO translation with bisimulation invariance of the mu-calculus.
-/
theorem finite_bisimulation_invariant_mso {P : Type} [Finite P]
    (L : Set (TransitionSystem P)) :
    (MonadicSecondOrder.Definable L ∧ BisimulationInvariant L) ↔
      ModalMuCalculus.Definable L := by
  constructor
  · rintro ⟨⟨φ, hφ⟩, hinv⟩
    let K : Language (TransitionAlphabet P) := {S | MonadicSecondOrder.Models (decode S) φ}
    have hK : ∀ S T, RankedBisimilar S T → (S ∈ K ↔ T ∈ K) := by
      intro S T h
      exact (hφ (decode S)).symm.trans
        ((hinv (decode S) (decode T) (Lax369799Proofs.RankedBisimulation.ranked_forward S T h)).trans
          (hφ (decode T)))
    obtain ⟨ψ, hψ⟩ := algebra_to_mu K hK (SupportedAlgebras.legacy_recognizable K (Lax369799Proofs.MSORecognition.mso_recognizable φ))
    refine ⟨ψ, ?_⟩
    intro S
    obtain ⟨T, rfl⟩ := Encoding.encoding_exists S
    exact (hφ (decode T)).trans (hψ T)
  · rintro ⟨φ, hφ⟩
    obtain ⟨ψ, hψ⟩ := MuToMSO.mu_to_mso φ
    refine ⟨⟨ψ, fun S => (hφ S).trans (hψ S)⟩, ?_⟩
    intro S T h
    exact (hφ S).trans ((MuBisimulation.mu_bisimulation_invariant φ S T h).trans (hφ T).symm)

/--
---
conclusion: Lax369799.FiniteBisimulationTheorem.effective_finite_bisimulation_invariant_mso
---
Apply the verified total finite-search compiler. Its bounded table list
contains an equivalent sentence under the invariance promise, and its
finite comparison bound separates every inequivalent candidate pair.
-/
theorem effective_finite_bisimulation_invariant_mso {P : Type}
    [Fintype P] [Encodable P] [DecidableEq P]
    (φ : MonadicSecondOrder.Sentence P)
    (hφ : BisimulationInvariant {S | MonadicSecondOrder.Models S φ}) :
    ∀ S : TransitionSystem P, MonadicSecondOrder.Models S φ ↔
      ModalMuCalculus.Models S (EffectiveFiniteTranslation.compile φ) :=
  EffectiveFiniteTranslation.compile_correct φ hφ

end Lax369799Proofs.MainTheorems
