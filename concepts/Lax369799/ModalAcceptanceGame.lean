import Lax369799.ModalTransitions
import Lax369799.ParityWinningRegions
import Lax369799.ParityGameEquations
import Mathlib.Data.Finset.Lattice.Fold

/-!
---
title: The finite modal acceptance game
type: theorem
---
At a position consisting of a word state and an input vertex, Eve chooses
a marking satisfying the modal transition. Adam chooses a marked successor.
An empty legal marking ends in the winning terminal; absence of any legal
marking ends in the losing terminal. Both terminals have self-loops, so the
arena is total. The two-move predecessor operation is exactly the modal
one-step condition. Reversed bounded priorities implement the least-even
word condition using the greatest-even convention of finite parity games.
-/

namespace Lax369799.ModalAcceptanceGame
open TransitionEncoding TransitionSystems UnfoldAutomata ModalTransitions FiniteParityGames

def Pre {V : Type} (G : Game V) (X : Set V) : Set V :=
  ParityWinningRegions.Pre G X

abbrev Marking {P : Type} (M : UnfoldAutomaton (TransitionAlphabet P))
    (S : TransitionSystem P) := Fin M.condition.states → Set S.Vertex

abbrev Vertex {P : Type} (M : UnfoldAutomaton (TransitionAlphabet P))
    (S : TransitionSystem P) :=
  (Fin M.condition.states × S.Vertex) ⊕ ((S.Vertex × Marking M S) ⊕ Bool)

def position {P : Type} {M : UnfoldAutomaton (TransitionAlphabet P)} {S : TransitionSystem P}
    (q : Fin M.condition.states) (v : S.Vertex) : Vertex M S := .inl (q, v)

def selection {P : Type} {M : UnfoldAutomaton (TransitionAlphabet P)} {S : TransitionSystem P}
    (v : S.Vertex) (ρ : Marking M S) : Vertex M S := .inr (.inl (v, ρ))

def terminal {P : Type} {M : UnfoldAutomaton (TransitionAlphabet P)} {S : TransitionSystem P}
    (b : Bool) : Vertex M S := .inr (.inr b)

def Edge {P : Type} (M : UnfoldAutomaton (TransitionAlphabet P)) (S : TransitionSystem P) :
    Vertex M S → Vertex M S → Prop
  | .inl (q, v), .inr (.inl (w, ρ)) => v = w ∧ OneStep M q S v ρ
  | .inl (q, v), .inr (.inr false) => ¬ ∃ ρ, OneStep M q S v ρ
  | .inr (.inl (v, ρ)), .inl (q, w) => S.edge v w ∧ w ∈ ρ q
  | .inr (.inl (v, ρ)), .inr (.inr true) => ¬ ∃ q w, S.edge v w ∧ w ∈ ρ q
  | .inr (.inr b), .inr (.inr c) => b = c
  | _, _ => False

def eve {P : Type} (M : UnfoldAutomaton (TransitionAlphabet P)) (S : TransitionSystem P) :
    Vertex M S → Prop
  | .inl _ => True
  | .inr _ => False

def ceiling {u z : ℕ} (D : WordCondition u z) : ℕ :=
  2 * (Finset.univ.sup D.priority + 1)

def priority {P : Type} (M : UnfoldAutomaton (TransitionAlphabet P)) (S : TransitionSystem P) :
    Vertex M S → ℕ
  | .inl (q, _) => ceiling M.condition - M.condition.priority q
  | .inr (.inr false) => 1
  | _ => 0

noncomputable def game {P : Type} (M : UnfoldAutomaton (TransitionAlphabet P))
    (S : TransitionSystem P) : Game (Vertex M S) where
  eve := eve M S
  edge := Edge M S
  priority := priority M S
  total := by
    classical
    intro v
    rcases v with ⟨q, v⟩ | (⟨v, ρ⟩ | b)
    · by_cases h : ∃ ρ, OneStep M q S v ρ
      · exact ⟨selection v h.choose, rfl, h.choose_spec⟩
      · exact ⟨terminal false, h⟩
    · by_cases h : ∃ q w, S.edge v w ∧ w ∈ ρ q
      · obtain ⟨q, w, h⟩ := h
        exact ⟨position q w, h⟩
      · exact ⟨terminal true, h⟩
    · exact ⟨terminal b, rfl⟩

def target {P : Type} (M : UnfoldAutomaton (TransitionAlphabet P))
    (S : TransitionSystem P) (X : Marking M S) : Set (Vertex M S)
  | .inl (q, v) => v ∈ X q
  | .inr (.inr true) => True
  | _ => False

axiom predecessor {P : Type} (M : UnfoldAutomaton (TransitionAlphabet P))
    (S : TransitionSystem P) (q : Fin M.condition.states) (v : S.Vertex) (X : Marking M S) :
    position q v ∈ Pre (game M S) (Pre (game M S) (target M S X)) ↔ OneStep M q S v X

axiom finite {P : Type} (M : UnfoldAutomaton (TransitionAlphabet P)) (S : TransitionSystem P) :
    Finite (Vertex M S)

axiom determined {P : Type} (M : UnfoldAutomaton (TransitionAlphabet P)) (S : TransitionSystem P) :
    ∃ f g : Vertex M S → Vertex M S,
      (game M S).Legal true f ∧ (game M S).Legal false g ∧
        ∀ v, (game M S).WinsFrom true f v ∨ (game M S).WinsFrom false g v

axiom priority_positive {u z : ℕ} (D : WordCondition u z) (q : Fin D.states) :
    0 < ceiling D - D.priority q

axiom reverse_parity {u z : ℕ} (D : WordCondition u z) (w : ℕ → Fin u) :
    D.AcceptsInfinite w ↔ ∃ c, Even c ∧
      (∀ N, ∃ n, N ≤ n ∧ ceiling D - D.priority (D.run w n) = c) ∧
      ∀ b, c < b → ¬ ∀ N, ∃ n, N ≤ n ∧ ceiling D - D.priority (D.run w n) = b

axiom terminal_winning {P : Type} (M : UnfoldAutomaton (TransitionAlphabet P))
    (S : TransitionSystem P) (b : Bool) :
    ParityWinningRegions.Winning (game M S) true (terminal b) ↔ b = true

axiom winning_equation {P : Type} (M : UnfoldAutomaton (TransitionAlphabet P))
    (S : TransitionSystem P) (q : Fin M.condition.states) (v : S.Vertex) :
    ParityWinningRegions.Winning (game M S) true (position q v) ↔
      OneStep M q S v (fun p => {w | ParityWinningRegions.Winning (game M S) true (position p w)})

axiom winning_nested {P : Type} (M : UnfoldAutomaton (TransitionAlphabet P))
    (S : TransitionSystem P) (q : Fin M.condition.states) (v : S.Vertex) :
    ParityWinningRegions.Winning (game M S) true (position q v) ↔
      position q v ∈ ParityGameEquations.solve (game M S) (ceiling M.condition + 1) (fun _ => ∅)

end Lax369799.ModalAcceptanceGame
