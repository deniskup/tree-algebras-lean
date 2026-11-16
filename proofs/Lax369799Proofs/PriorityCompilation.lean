import Lax369799.PriorityCompilation
import Lax369799Proofs.ModalGameEquations
import Lax369799Proofs.FiniteMuEquations

set_option backward.isDefEq.respectTransparency false

namespace Lax369799Proofs.PriorityCompilation
open Lax369799
open TransitionSystems TransitionEncoding UnfoldAutomata ModalTransitions ModalAcceptanceGame
open ModalMuCalculus MuSubstitution
open Lax369799.ModalGameEquations (statePriority)

open Lax369799.PriorityCompilation

private theorem boundary_eval {P : Type}
    (M : UnfoldAutomaton (TransitionAlphabet P)) (S : TransitionSystem P) {m : ℕ}
    (n : ℕ) (θ : ℕ → Fin M.condition.states → Formula P m)
    (ρ : Fin m → Set S.Vertex) (X : Marking M S) :
    (fun p q => (boundary n θ p q).eval S (Fin.addCases X ρ)) =
      Function.update (fun p q => (θ p q).eval S ρ) n X := by
  funext p q
  by_cases h : p = n
  · subst p
    simp [boundary, Formula.eval]
  · simp only [boundary, if_neg h, Function.update_of_ne h]
    rw [MuSubstitution.eval_rename]
    congr 1
    funext i
    simp

/--
---
conclusion: Lax369799.PriorityCompilation.compile_correct
---
Induct over the priority binders, using formula substitution and scalar elimination of each finite simultaneous fixed point.
-/
theorem compile_correct {P : Type}
    (M : UnfoldAutomaton (TransitionAlphabet P))
    (δ : Fin M.condition.states → Formula P M.condition.states)
    (S : TransitionSystem P)
    (hδ : ∀ q ρ v, v ∈ (δ q).eval S ρ ↔ OneStep M q S v ρ)
    (n : ℕ) {m : ℕ} (θ : ℕ → Fin M.condition.states → Formula P m)
    (ρ : Fin m → Set S.Vertex) :
    (fun q => (compile (statePriority M) δ n θ q).eval S ρ) =
      Lax369799.ModalGameEquations.solve M S n (fun p q => (θ p q).eval S ρ) := by
  induction n generalizing m with
  | zero =>
    funext q
    ext v
    change v ∈ (substitute _ (δ q)).eval S ρ ↔ _
    rw [MuSubstitution.eval_substitute]
    exact hδ q _ v
  | succ n ih =>
    have hb (X : Marking M S) :
        (fun q => (compile (statePriority M) δ n (boundary n θ) q).eval S (Fin.addCases X ρ)) =
          Lax369799.ModalGameEquations.solve M S n
            (Function.update (fun p q => (θ p q).eval S ρ) n X) := by
      rw [ih, boundary_eval]
    change (fun q => (Lax369799.FiniteMuEquations.solve _ _ q).eval S ρ) = _
    rw [FiniteMuEquations.solve_correct]
    by_cases h : Even n
    · simp only [Lax369799.FiniteMuEquations.value,
        Lax369799.ModalGameEquations.solve, if_pos ((Nat.even_iff).mp h), if_pos h]
      congr 1
      ext X
      simp only [Set.mem_ofPred_eq]
      rw [← hb X]
      rfl
    · simp only [Lax369799.FiniteMuEquations.value,
        Lax369799.ModalGameEquations.solve, if_neg (fun hmod => h ((Nat.even_iff).mpr hmod)), if_neg h]
      congr 1
      ext X
      simp only [Set.mem_ofPred_eq]
      rw [← hb X]
      rfl

/--
---
conclusion: Lax369799.PriorityCompilation.sentence_correct
---
Instantiate the proved finite priority equations at their full depth.
-/
theorem sentence_correct {P : Type} (M : UnfoldAutomaton (TransitionAlphabet P))
    (δ : Fin M.condition.states → Formula P M.condition.states)
    (S : TransitionSystem P)
    (hδ : ∀ q ρ v, v ∈ (δ q).eval S ρ ↔ OneStep M q S v ρ) :
    Models S (sentence (statePriority M) δ (ceiling M.condition+1) M.condition.initial) ↔
      Lax369799.ParityWinningRegions.Winning (game M S) true (position M.condition.initial S.initial) := by
  have hf := compile_correct M δ S hδ (ceiling M.condition+1)
    (fun _ _ => (Formula.bot : Formula P 0)) Fin.elim0
  have hw := ModalGameEquations.winning M S (ceiling M.condition+1)
    (fun q => by unfold statePriority; omega) (fun _ _ => ∅)
  have he : (sentence (statePriority M) δ (ceiling M.condition+1) M.condition.initial).eval S Fin.elim0 =
      Lax369799.ModalGameEquations.project M S
        (Lax369799.ParityWinningRegions.Winning (game M S) true) M.condition.initial := by
    exact (congrFun hf M.condition.initial).trans (congrFun hw.symm M.condition.initial)
  unfold Models
  rw [he]
  rfl

end Lax369799Proofs.PriorityCompilation
