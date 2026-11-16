import Lax369799.ModalGameTranslation
import Lax369799Proofs.ModalGameEquations
import Lax369799Proofs.FiniteMuEquations

set_option backward.isDefEq.respectTransparency false

namespace Lax369799Proofs.ModalGameTranslation
open Lax369799
open TransitionSystems TransitionEncoding UnfoldAutomata ModalTransitions ModalAcceptanceGame
open ModalMuCalculus MuSubstitution
open Lax369799.ModalGameEquations (statePriority)
attribute [local instance] Classical.propDecidable

open Lax369799.ModalGameTranslation

private theorem boundary_eval {P : Type}
    (M : UnfoldAutomaton (TransitionAlphabet P)) (S : TransitionSystem P) {m : ℕ}
    (n : ℕ) (θ : ℕ → Fin M.condition.states → Formula P m)
    (ρ : Fin m → Set S.Vertex) (X : Marking M S) :
    (fun p q => (bindBoundary M n θ p q).eval S (Fin.addCases X ρ)) =
      Function.update (fun p q => (θ p q).eval S ρ) n X := by
  funext p q
  by_cases h : p = n
  · subst p
    simp [bindBoundary, Formula.eval]
  · simp only [bindBoundary, if_neg h, Function.update_of_ne h]
    rw [MuSubstitution.eval_rename]
    congr 1
    funext i
    simp

/--
---
conclusion: Lax369799.ModalGameTranslation.formulas_correct
---
Induct over the priority binders, using formula substitution and scalar elimination of each finite simultaneous fixed point.
-/
theorem formulas_correct {P : Type} [Fintype P]
    (M : UnfoldAutomaton (TransitionAlphabet P)) (S : TransitionSystem P)
    (n : ℕ) {m : ℕ} (θ : ℕ → Fin M.condition.states → Formula P m)
    (ρ : Fin m → Set S.Vertex) :
    (fun q => (formulas M n θ q).eval S ρ) =
      Lax369799.ModalGameEquations.solve M S n (fun p q => (θ p q).eval S ρ) := by
  induction n generalizing m with
  | zero =>
    funext q
    ext v
    change v ∈ (substitute _ (transitionFormula M q)).eval S ρ ↔ _
    rw [MuSubstitution.eval_substitute]
    exact ModalTransitions.eval_transition M q S _ v
  | succ n ih =>
    have hb (X : Marking M S) :
        (fun q => (formulas M n (bindBoundary M n θ) q).eval S (Fin.addCases X ρ)) =
          Lax369799.ModalGameEquations.solve M S n
            (Function.update (fun p q => (θ p q).eval S ρ) n X) := by
      rw [ih, boundary_eval]
    change (fun q => (Lax369799.FiniteMuEquations.solve _ _ q).eval S ρ) = _
    rw [FiniteMuEquations.solve_correct]
    by_cases h : Even n
    · simp only [Lax369799.FiniteMuEquations.value,
        Lax369799.ModalGameEquations.solve, if_pos h]
      congr 1
      ext X
      simp only [Set.mem_ofPred_eq]
      rw [← hb X]
      rfl
    · simp only [Lax369799.FiniteMuEquations.value,
        Lax369799.ModalGameEquations.solve, if_neg h]
      congr 1
      ext X
      simp only [Set.mem_ofPred_eq]
      rw [← hb X]
      rfl

/--
---
conclusion: Lax369799.ModalGameTranslation.sentence_correct
---
Use the full priority bound in the projected winning-region equations and instantiate all remaining boundary parameters by bottom.
-/
theorem sentence_correct {P : Type} [Fintype P]
    (M : UnfoldAutomaton (TransitionAlphabet P)) (S : TransitionSystem P)
    (q : Fin M.condition.states) (v : S.Vertex) :
    v ∈ (sentence M q).eval S Fin.elim0 ↔
      Lax369799.ParityWinningRegions.Winning (game M S) true (position q v) := by
  have hf := formulas_correct M S (ceiling M.condition + 1) (fun _ _ => (Formula.bot : Formula P 0)) Fin.elim0
  have hw := ModalGameEquations.winning M S (ceiling M.condition + 1)
    (fun q => by unfold statePriority; omega) (fun _ _ => ∅)
  have he : (sentence M q).eval S Fin.elim0 =
      Lax369799.ModalGameEquations.project M S
        (Lax369799.ParityWinningRegions.Winning (game M S) true) q := by
    exact (congrFun hf q).trans (congrFun hw.symm q)
  rw [he]
  rfl

/--
---
conclusion: Lax369799.ModalGameTranslation.game_to_mu
---
Select the formula for the initial word state. The same sentence works on every finite input transition system.
-/
theorem game_to_mu {P : Type} [Finite P]
    (M : UnfoldAutomaton (TransitionAlphabet P)) :
    ∃ φ : Sentence P, ∀ S,
      Lax369799.ParityWinningRegions.Winning (game M S) true
        (position M.condition.initial S.initial) ↔ Models S φ := by
  classical
  let := Fintype.ofFinite P
  exact ⟨sentence M M.condition.initial, fun S => (sentence_correct M S _ S.initial).symm⟩

end Lax369799Proofs.ModalGameTranslation
