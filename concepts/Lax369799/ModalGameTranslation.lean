import Lax369799.ModalGameEquations
import Lax369799.FiniteMuEquations

/-!
---
title: Translating the modal acceptance game to a sentence
type: theorem
---
Translate the projected priority equations into formulas by binding a
finite vector of variables at each priority. Capture-avoiding substitution
supplies the boundary parameters; finite equation elimination implements
each vector binder in the scalar mu-calculus. The resulting sentence is
independent of the input graph and defines the game's winning region.
-/
namespace Lax369799.ModalGameTranslation
open TransitionSystems TransitionEncoding UnfoldAutomata ModalTransitions ModalAcceptanceGame
open ModalMuCalculus MuSubstitution
open ModalGameEquations (statePriority)
attribute [local instance] Classical.propDecidable

noncomputable def bindBoundary {P : Type}
    (M : UnfoldAutomaton (TransitionAlphabet P)) {m : ℕ}
    (n : ℕ) (θ : ℕ → Fin M.condition.states → Formula P m) :
    ℕ → Fin M.condition.states → Formula P (M.condition.states + m) :=
  fun p q => if p = n then .variable (Fin.castAdd m q)
    else rename (Fin.natAdd M.condition.states) (θ p q)

noncomputable def formulas {P : Type} [Fintype P]
    (M : UnfoldAutomaton (TransitionAlphabet P)) :
    (n : ℕ) → {m : ℕ} → (ℕ → Fin M.condition.states → Formula P m) →
      Fin M.condition.states → Formula P m
  | 0, _, θ => fun q => substitute (θ (statePriority M q)) (transitionFormula M q)
  | n + 1, _, θ => Lax369799.FiniteMuEquations.solve
      (if Even n then .greatest else .least) (formulas M n (bindBoundary M n θ))

noncomputable def sentence {P : Type} [Fintype P]
    (M : UnfoldAutomaton (TransitionAlphabet P)) (q : Fin M.condition.states) : Sentence P :=
  formulas M (ceiling M.condition + 1) (fun _ _ => .bot) q

axiom formulas_correct {P : Type} [Fintype P]
    (M : UnfoldAutomaton (TransitionAlphabet P)) (S : TransitionSystem P)
    (n : ℕ) {m : ℕ} (θ : ℕ → Fin M.condition.states → Formula P m)
    (ρ : Fin m → Set S.Vertex) :
    (fun q => (formulas M n θ q).eval S ρ) =
      Lax369799.ModalGameEquations.solve M S n (fun p q => (θ p q).eval S ρ)

axiom sentence_correct {P : Type} [Fintype P]
    (M : UnfoldAutomaton (TransitionAlphabet P)) (S : TransitionSystem P)
    (q : Fin M.condition.states) (v : S.Vertex) :
    v ∈ (sentence M q).eval S Fin.elim0 ↔
      Lax369799.ParityWinningRegions.Winning (game M S) true (position q v)

axiom game_to_mu {P : Type} [Finite P]
    (M : UnfoldAutomaton (TransitionAlphabet P)) :
    ∃ φ : Sentence P, ∀ S,
      Lax369799.ParityWinningRegions.Winning (game M S) true
        (position M.condition.initial S.initial) ↔ Models S φ

end Lax369799.ModalGameTranslation
