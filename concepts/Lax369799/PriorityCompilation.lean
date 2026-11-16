import Lax369799.FiniteMuEquations
import Lax369799.ModalGameEquations

/-!
---
title: Executable compilation of modal priority equations
type: theorem
---
An explicit finite family of positive modal transition formulas and a
priority map compile to a scalar sentence by structural recursion. The
compiler uses only finite syntax operations. A semantic certificate for
the transition formulas identifies its output with the modal acceptance
game. This is the effective final stage, with the finite transition table
provided as input.
-/

namespace Lax369799.PriorityCompilation
open ModalMuCalculus MuSubstitution TransitionEncoding TransitionSystems UnfoldAutomata
open ModalAcceptanceGame

def boundary {P : Type} {d m : ℕ} (n : ℕ)
    (θ : ℕ → Fin d → Formula P m) : ℕ → Fin d → Formula P (d+m) :=
  fun p q => if p = n then .variable (Fin.castAdd m q)
    else rename (Fin.natAdd d) (θ p q)

def compile {P : Type} {d : ℕ} (priority : Fin d → ℕ)
    (transition : Fin d → Formula P d) :
    (n : ℕ) → {m : ℕ} → (ℕ → Fin d → Formula P m) → Fin d → Formula P m
  | 0, _, θ => fun q => substitute (θ (priority q)) (transition q)
  | n+1, _, θ => FiniteMuEquations.solve
      (if n % 2 = 0 then .greatest else .least) (compile priority transition n (boundary n θ))

def sentence {P : Type} {d : ℕ} (priority : Fin d → ℕ)
    (transition : Fin d → Formula P d) (depth : ℕ) (initial : Fin d) : Sentence P :=
  compile priority transition depth (fun _ _ => .bot) initial

axiom compile_correct {P : Type} (M : UnfoldAutomaton (TransitionAlphabet P))
    (δ : Fin M.condition.states → Formula P M.condition.states)
    (S : TransitionSystem P)
    (hδ : ∀ q ρ v, v ∈ (δ q).eval S ρ ↔ ModalTransitions.OneStep M q S v ρ)
    (n : ℕ) {m : ℕ} (θ : ℕ → Fin M.condition.states → Formula P m)
    (ρ : Fin m → Set S.Vertex) :
    (fun q => (compile (ModalGameEquations.statePriority M) δ n θ q).eval S ρ) =
      ModalGameEquations.solve M S n (fun p q => (θ p q).eval S ρ)

axiom sentence_correct {P : Type} (M : UnfoldAutomaton (TransitionAlphabet P))
    (δ : Fin M.condition.states → Formula P M.condition.states)
    (S : TransitionSystem P)
    (hδ : ∀ q ρ v, v ∈ (δ q).eval S ρ ↔ ModalTransitions.OneStep M q S v ρ) :
    Models S (sentence (ModalGameEquations.statePriority M) δ (ceiling M.condition+1)
      M.condition.initial) ↔
      ParityWinningRegions.Winning (game M S) true (position M.condition.initial S.initial)

end Lax369799.PriorityCompilation
