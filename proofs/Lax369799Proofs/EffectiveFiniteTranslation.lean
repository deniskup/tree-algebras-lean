import Lax369799.EffectiveFiniteTranslation
import Lax369799.QuantitativeFiniteTheorem
import Lax369799Proofs.FiniteTesting
import Lax369799Proofs.QuantitativeFiniteTheorem
import Lax369799Proofs.MuBisimulation
import Mathlib.Data.List.ProdSigma

set_option backward.isDefEq.respectTransparency false
namespace Lax369799Proofs.EffectiveFiniteTranslation
open Lax369799
open TransitionSystems ModalMuCalculus
open Lax369799.EffectiveFiniteTranslation

private theorem candidate_complete {P : Type} [Fintype P] [Encodable P] [DecidableEq P]
    (φ : MonadicSecondOrder.Sentence P)
    (hφ : BisimulationInvariant {S | MonadicSecondOrder.Models S φ}) :
    ∃ ψ ∈ candidates φ,∀ S,MonadicSecondOrder.Models S φ ↔ Models S ψ := by
  obtain ⟨M,hu,hz,hd,hp,he⟩ := QuantitativeFiniteTheorem.modal_certificate φ hφ
  obtain ⟨t,ht⟩ := FiniteModalData.exists_table M
    (QuantitativeAutomata.priorityBound (QuantitativeRecognition.msoBound φ)) hp
  refine ⟨FiniteModalData.compile t,?_,fun S => (he S).trans (ht S).symm⟩
  simp only [candidates,List.mem_flatMap,List.mem_map,List.mem_range]
  exact ⟨M.unary,Nat.lt_succ_of_le hu,M.nullary,Nat.lt_succ_of_le hz,
    M.condition.states,Nat.lt_succ_of_le hd,t,FiniteModalData.mem_elements _ t,rfl⟩

/--
---
conclusion: Lax369799.EffectiveFiniteTranslation.mu_translation_correct
---
The syntactic translation on arbitrary structures specializes to the
finite semantics, providing the effective reverse direction of Theorem 2.
-/
theorem mu_translation_correct {P : Type} (ψ : Sentence P) (S : TransitionSystem P) :
    Models S ψ ↔ MonadicSecondOrder.Models S (UnrestrictedLogic.sentence ψ) := by
  have h : UnrestrictedLogic.MuModels (UnrestrictedTransitionSystems.ofFinite S) ψ ↔
      UnrestrictedLogic.MSOModels (UnrestrictedTransitionSystems.ofFinite S) (UnrestrictedLogic.sentence ψ) := by
    simp [UnrestrictedLogic.sentence,UnrestrictedLogic.conjunction,UnrestrictedLogic.MSOModels,
      UnrestrictedLogic.msoEval,UnrestrictedLogic.translate_correct,UnrestrictedLogic.MuModels]
  exact (UnrestrictedLogic.finite_mu_models S ψ).symm.trans
    (h.trans (UnrestrictedLogic.finite_mso_models S (UnrestrictedLogic.sentence ψ)))

private theorem difference_correct {P : Type} (ψ χ : Sentence P) (S : TransitionSystem P) :
    MonadicSecondOrder.Models S (difference ψ χ) ↔ ¬(Models S ψ ↔ Models S χ) := by
  have hψ := mu_translation_correct ψ S
  have hχ := mu_translation_correct χ S
  simp only [difference,conjunction,MonadicSecondOrder.Models,MonadicSecondOrder.Formula.eval]
  change ((¬(¬MonadicSecondOrder.Models S (UnrestrictedLogic.sentence ψ) ∨
    ¬¬MonadicSecondOrder.Models S (UnrestrictedLogic.sentence χ))) ∨
    ¬(¬¬MonadicSecondOrder.Models S (UnrestrictedLogic.sentence ψ) ∨
      ¬MonadicSecondOrder.Models S (UnrestrictedLogic.sentence χ))) ↔ _
  rw [← hψ,← hχ]
  by_cases hp : Models S ψ <;> by_cases hc : Models S χ <;> simp [hp,hc]

private theorem difference_invariant {P : Type} (ψ χ : Sentence P) :
    BisimulationInvariant {S | MonadicSecondOrder.Models S (difference ψ χ)} := by
  intro S T hb
  change MonadicSecondOrder.Models S (difference ψ χ) ↔ MonadicSecondOrder.Models T (difference ψ χ)
  rw [difference_correct,difference_correct]
  exact not_congr (iff_congr (MuBisimulation.mu_bisimulation_invariant ψ S T hb)
    (MuBisimulation.mu_bisimulation_invariant χ S T hb))

private theorem separation {P : Type} [Finite P] (ψ χ : Sentence P)
    (h : ∃ S,¬(Models S ψ ↔ Models S χ)) :
    ∃ T : TransitionSystem P,T.size ≤ QuantitativeFiniteTheorem.modelBound (difference ψ χ) ∧
      ¬(Models T ψ ↔ Models T χ) := by
  have hm : ∃ S,MonadicSecondOrder.Models S (difference ψ χ) := by
    obtain ⟨S,hS⟩ := h
    exact ⟨S,(difference_correct ψ χ S).mpr hS⟩
  obtain ⟨T,hb,hT⟩ := QuantitativeFiniteTheorem.nonempty_bound
    (difference ψ χ) (difference_invariant ψ χ) hm
  exact ⟨T,hb,(difference_correct ψ χ T).mp hT⟩

private theorem mem_fold_max {l : List ℕ} (n : ℕ) (h : n ∈ l) : n ≤ l.foldr max 0 := by
  induction l with
  | nil => exact False.elim (List.not_mem_nil h)
  | cons a l ih =>
    rcases List.mem_cons.mp h with rfl | h
    · exact Nat.le_max_left _ _
    · exact (ih h).trans (Nat.le_max_right _ _)

private theorem pair_bound {P : Type} (cs : List (Sentence P)) (ψ χ : Sentence P)
    (hψ : ψ ∈ cs) (hχ : χ ∈ cs) :
    QuantitativeFiniteTheorem.modelBound (difference ψ χ) ≤ separationBound cs :=
  mem_fold_max _ (List.mem_map.mpr ⟨(ψ,χ),List.mem_product.mpr ⟨hψ,hχ⟩,rfl⟩)

/--
Enumerate all bounded Boolean modal tables and compile their sentences.
One candidate agrees with the invariant input by the quantitative finite
theorem. Test candidates on every reachable graph within the maximum
pair-separation bound. Any selected candidate agrees there with the true
candidate, hence agrees on every finite system. The fallback is reached
only when the promise does not provide a passing candidate.
The main effective theorem registers this correctness result with the Archive.
-/
theorem compile_correct {P : Type} [Fintype P] [Encodable P] [DecidableEq P]
    (φ : MonadicSecondOrder.Sentence P)
    (hφ : BisimulationInvariant {S | MonadicSecondOrder.Models S φ}) :
    ∀ S : TransitionSystem P,MonadicSecondOrder.Models S φ ↔ Models S (compile φ) := by
  classical
  let cs := candidates φ
  let K := separationBound cs
  let pred := fun ψ => FiniteTesting.test K φ ψ
  obtain ⟨ψ0,h0,he0⟩ := candidate_complete φ hφ
  have hp0 : pred ψ0 = true := (FiniteTesting.test_correct K φ ψ0).mpr (fun S _ => he0 S)
  cases hf : cs.find? pred with
  | none =>
    have hn := List.find?_eq_none.mp hf ψ0 h0
    exact False.elim (hn hp0)
  | some ψ =>
    have hm : ψ ∈ cs := List.mem_of_find?_eq_some hf
    have hp : pred ψ = true := List.find?_some hf
    have htested := (FiniteTesting.test_correct K φ ψ).mp hp
    have heq : ∀ S : TransitionSystem P,Models S ψ ↔ Models S ψ0 := by
      intro S
      by_contra hS
      obtain ⟨T,hb,hdiff⟩ := separation ψ ψ0 ⟨S,hS⟩
      have ht := htested T (hb.trans (pair_bound cs ψ ψ0 hm h0))
      exact hdiff (ht.symm.trans (he0 T))
    have hcompiled : compile φ = ψ := by
      change (cs.find? pred).getD .bot = ψ
      rw [hf]
      rfl
    intro S
    rw [hcompiled]
    exact (he0 S).trans (heq S).symm

end Lax369799Proofs.EffectiveFiniteTranslation
