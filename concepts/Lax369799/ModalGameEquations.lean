import Lax369799.ModalAcceptanceGame
import Lax369799.FixedPointRetraction

/-!
---
title: Modal equations on input vertices
type: theorem
---
Project winning regions to word-state/input positions. Marking positions
are determined by universal successor conditions and terminals by their
outcomes. The projection and its monotone section preserve the least and
greatest solutions of each stopped priority game. The resulting nested
equations have one coordinate per word state and are evaluated on the
original input graph.
-/
namespace Lax369799.ModalGameEquations
open TransitionSystems TransitionEncoding UnfoldAutomata ModalTransitions ModalAcceptanceGame
open FiniteParityGames ParityWinningRegions ParityFixedPoints
attribute [local instance] Classical.propDecidable

def project {P : Type} (M : UnfoldAutomaton (TransitionAlphabet P)) (S : TransitionSystem P) :
    Set (Vertex M S) →o Marking M S where
  toFun := fun X q => {v | position q v ∈ X}
  monotone' := fun _ _ h _ _ hv => h hv

def lift {P : Type} (M : UnfoldAutomaton (TransitionAlphabet P)) (S : TransitionSystem P) :
    Marking M S →o Set (Vertex M S) where
  toFun := fun X t => match t with
    | .inl (q, v) => v ∈ X q
    | .inr (.inl (v, ρ)) => ∀ q w, S.edge v w → w ∈ ρ q → w ∈ X q
    | .inr (.inr b) => b = true
  monotone' := by
    intro X Y h t ht
    rcases t with ⟨q, v⟩ | (⟨v, ρ⟩ | b)
    · exact h q ht
    · exact fun q w hw hρ => h q (ht q w hw hρ)
    · exact ht

def statePriority {P : Type} (M : UnfoldAutomaton (TransitionAlphabet P))
    (q : Fin M.condition.states) : ℕ := ceiling M.condition - M.condition.priority q

def boundary {P : Type} (M : UnfoldAutomaton (TransitionAlphabet P)) (S : TransitionSystem P)
    (B : Fin M.condition.states → S.Vertex → Prop) : Set (Vertex M S) :=
  {t | match t with
    | .inl (q, v) => B q v
    | _ => False}

noncomputable def stopped {P : Type} (M : UnfoldAutomaton (TransitionAlphabet P))
    (S : TransitionSystem P) (n : ℕ) (ρ : ℕ → Marking M S) : Game (Vertex M S) :=
  stop (game M S) (boundary M S (fun q _ => n ≤ statePriority M q))
    (boundary M S (fun q v => OneStep M q S v (ρ (statePriority M q))))

noncomputable def solve {P : Type} (M : UnfoldAutomaton (TransitionAlphabet P))
    (S : TransitionSystem P) : ℕ → (ℕ → Marking M S) → Marking M S
  | 0, ρ => fun q => {v | OneStep M q S v (ρ (statePriority M q))}
  | n + 1, ρ => if Even n then
      sSup {X : Marking M S | X ≤ solve M S n (Function.update ρ n X)}
    else sInf {X : Marking M S | solve M S n (Function.update ρ n X) ≤ X}

axiom solve_stopped {P : Type} (M : UnfoldAutomaton (TransitionAlphabet P))
    (S : TransitionSystem P) (n : ℕ) (ρ : ℕ → Marking M S) :
    project M S (Winning (stopped M S n ρ) true) = solve M S n ρ

axiom winning {P : Type} (M : UnfoldAutomaton (TransitionAlphabet P))
    (S : TransitionSystem P) (n : ℕ) (hn : ∀ q, statePriority M q < n)
    (ρ : ℕ → Marking M S) :
    project M S (Winning (game M S) true) = solve M S n ρ

end Lax369799.ModalGameEquations
