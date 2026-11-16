import Lax369799.ModalAcceptanceGame
import Lax369799Proofs.ModalTransitions
import Lax369799Proofs.ParityWinningRegions
import Lax369799Proofs.ParityGameEquations

namespace Lax369799Proofs.ModalAcceptanceGame
open Lax369799
open TransitionEncoding TransitionSystems UnfoldAutomata ModalTransitions FiniteParityGames
open Lax369799.ModalAcceptanceGame

private theorem selection_pre {P : Type} (M : UnfoldAutomaton (TransitionAlphabet P))
    (S : TransitionSystem P) (v : S.Vertex) (ρ X : Marking M S) :
    selection v ρ ∈ Pre (game M S) (target M S X) ↔
      ∀ q w, S.edge v w → w ∈ ρ q → w ∈ X q := by
  constructor
  · intro h q w hw hρ
    exact h.2 (fun h => h) (position q w) ⟨hw, hρ⟩
  · intro h
    refine ⟨fun h => h.elim, ?_⟩
    intro _ w hw
    rcases w with ⟨q, w⟩ | (⟨w, σ⟩ | b)
    · exact h q w hw.1 hw.2
    · exact hw.elim
    · cases b
      · exact hw.elim
      · trivial

private theorem terminal_pre {P : Type} (M : UnfoldAutomaton (TransitionAlphabet P))
    (S : TransitionSystem P) (X : Marking M S) (b : Bool) :
    terminal b ∈ Pre (game M S) (target M S X) ↔ b = true := by
  cases b
  · constructor
    · intro h
      exact (h.2 (fun h => h) (terminal false) rfl).elim
    · intro h; cases h
  · refine ⟨fun _ => rfl, fun _ => ⟨fun h => h.elim, ?_⟩⟩
    intro _ w hw
    rcases w with ⟨q, w⟩ | (⟨w, σ⟩ | b)
    · exact hw.elim
    · exact hw.elim
    · cases b
      · cases hw
      · trivial

/--
---
conclusion: Lax369799.ModalAcceptanceGame.predecessor
---
Eve can choose a legal marking all of whose responses meet the target
exactly when the target itself satisfies the positive one-step condition.
-/
theorem predecessor {P : Type} (M : UnfoldAutomaton (TransitionAlphabet P))
    (S : TransitionSystem P) (q : Fin M.condition.states) (v : S.Vertex) (X : Marking M S) :
    position q v ∈ Pre (game M S) (Pre (game M S) (target M S X)) ↔ OneStep M q S v X := by
  constructor
  · intro h
    obtain ⟨w, hw, hpre⟩ := h.1 trivial
    rcases w with ⟨p, w⟩ | (⟨w, ρ⟩ | b)
    · exact hw.elim
    · obtain ⟨rfl, hρ⟩ := hw
      have hb := (selection_pre M S v ρ X).mp hpre
      rcases hρ with h | ⟨B, hB, hl, hr⟩
      · exact Or.inl h
      · refine Or.inr ⟨B, hB, ?_, ?_⟩
        · intro b hb'
          obtain ⟨w, hw, hw'⟩ := hl b hb'
          exact ⟨w, hw, hb _ w hw hw'⟩
        · intro w hw
          obtain ⟨b, hb', hw'⟩ := hr w hw
          exact ⟨b, hb', hb _ w hw hw'⟩
    · cases b
      · exact False.elim (Bool.false_ne_true ((terminal_pre M S X false).mp hpre))
      · exact hw.elim
  · intro h
    refine ⟨fun _ => ⟨selection v X, ⟨rfl, h⟩,
      (selection_pre M S v X X).mpr (fun _ _ _ h => h)⟩, ?_⟩
    intro h
    exact (h trivial).elim

/--
---
conclusion: Lax369799.ModalAcceptanceGame.finite
---
The word states, input vertices, and sets of state-successor pairs are finite.
-/
theorem finite {P : Type} (M : UnfoldAutomaton (TransitionAlphabet P)) (S : TransitionSystem P) :
    Finite (Vertex M S) := by
  infer_instance

/--
---
conclusion: Lax369799.ModalAcceptanceGame.determined
---
The terminal self-loops make the finite arena total, so positional
determinacy applies including failed transitions and accepting leaves.
-/
theorem determined {P : Type} (M : UnfoldAutomaton (TransitionAlphabet P)) (S : TransitionSystem P) :
    ∃ f g : Vertex M S → Vertex M S,
      (game M S).Legal true f ∧ (game M S).Legal false g ∧
        ∀ v, (game M S).WinsFrom true f v ∨ (game M S).WinsFrom false g v := by
  let := finite M S
  exact FiniteParityGames.positional_determinacy (game M S)

private theorem priority_lt {u z : ℕ} (D : WordCondition u z) (q : Fin D.states) :
    D.priority q < ceiling D := by
  have h := Finset.le_sup (f := D.priority) (Finset.mem_univ q)
  unfold ceiling
  omega

/--
---
conclusion: Lax369799.ModalAcceptanceGame.priority_positive
---
The even ceiling lies strictly above every word-state priority, so the
zero priorities on intermediate choices do not determine parity.
-/
theorem priority_positive {u z : ℕ} (D : WordCondition u z) (q : Fin D.states) :
    0 < ceiling D - D.priority q := by
  have := priority_lt D q
  omega

/--
---
conclusion: Lax369799.ModalAcceptanceGame.reverse_parity
---
Subtraction from an even ceiling preserves parity and reverses the order
of recurrent priorities. Every priority lies strictly below the ceiling.
-/
theorem reverse_parity {u z : ℕ} (D : WordCondition u z) (w : ℕ → Fin u) :
    D.AcceptsInfinite w ↔ ∃ c, Even c ∧
      (∀ N, ∃ n, N ≤ n ∧ ceiling D - D.priority (D.run w n) = c) ∧
      ∀ b, c < b → ¬ ∀ N, ∃ n, N ≤ n ∧ ceiling D - D.priority (D.run w n) = b := by
  classical
  have heven : Even (ceiling D) := ⟨Finset.univ.sup D.priority + 1, by unfold ceiling; omega⟩
  have hbound : ∀ n, D.priority (D.run w n) < ceiling D := fun n => priority_lt D _
  constructor
  · rintro ⟨c, hc, hrec, hmin⟩
    have hcB : c ≤ ceiling D := by
      obtain ⟨n, _, hn⟩ := hrec 0
      have := hbound n
      omega
    refine ⟨ceiling D - c, (Nat.even_sub hcB).mpr ⟨fun _ => hc, fun _ => heven⟩, ?_, ?_⟩
    · intro N
      obtain ⟨n, hn, he⟩ := hrec N
      exact ⟨n, hn, by rw [he]⟩
    · intro b hb hrec'
      have hbB : b ≤ ceiling D := by
        obtain ⟨n, _, hn⟩ := hrec' 0
        omega
      obtain ⟨N, hN⟩ := hmin (ceiling D - b) (by omega)
      obtain ⟨n, hn, he⟩ := hrec' N
      have := hbound n
      exact hN n hn (by omega)
  · rintro ⟨c, hc, hrec, hmax⟩
    have hcB : c ≤ ceiling D := by
      obtain ⟨n, _, hn⟩ := hrec 0
      omega
    refine ⟨ceiling D - c, (Nat.even_sub hcB).mpr ⟨fun _ => hc, fun _ => heven⟩, ?_, ?_⟩
    · intro N
      obtain ⟨n, hn, he⟩ := hrec N
      have := hbound n
      exact ⟨n, hn, by omega⟩
    · intro b hb
      by_contra h
      push Not at h
      apply hmax (ceiling D - b) (by omega)
      intro N
      obtain ⟨n, hn, he⟩ := h N
      exact ⟨n, hn, by rw [he]⟩

private theorem terminal_path {P : Type} (M : UnfoldAutomaton (TransitionAlphabet P))
    (S : TransitionSystem P) (b : Bool) (p : ℕ → Vertex M S)
    (hp : (game M S).IsPlay p) (hp0 : p 0 = terminal b) :
    ∀ n, p n = terminal b := by
  intro n
  induction n with
  | zero => exact hp0
  | succ n ih =>
    have he := hp n
    rw [ih] at he
    rcases h : p (n + 1) with ⟨q, v⟩ | (⟨v, ρ⟩ | c)
    · rw [h] at he
      exact he.elim
    · rw [h] at he
      exact he.elim
    · rw [h] at he
      exact congrArg terminal he.symm

/--
---
conclusion: Lax369799.ModalAcceptanceGame.terminal_winning
---
Every play starting at a terminal remains there. The two constant
priority sequences have priorities zero and one respectively.
-/
theorem terminal_winning {P : Type} (M : UnfoldAutomaton (TransitionAlphabet P))
    (S : TransitionSystem P) (b : Bool) :
    Lax369799.ParityWinningRegions.Winning (game M S) true (terminal b) ↔ b = true := by
  classical
  cases b
  · constructor
    · rintro ⟨f, hf, hw⟩
      have hp : (game M S).IsPlay (fun _ => terminal false) := fun _ => rfl
      have hc : (game M S).Consistent true f (fun _ => terminal false) :=
        fun _ h => (h.mpr rfl).elim
      obtain ⟨c, ⟨hrec, _⟩, heven⟩ := (hw _ hp rfl hc).mpr rfl
      obtain ⟨n, _, hn⟩ := hrec 0
      change 1 = c at hn
      subst c
      simp at heven
    · intro h; cases h
  · refine ⟨fun _ => rfl, fun _ => ?_⟩
    let f : Vertex M S → Vertex M S := fun v => Classical.choose ((game M S).total v)
    refine ⟨f, fun v _ => Classical.choose_spec ((game M S).total v), ?_⟩
    intro p hp hp0 _
    refine ⟨fun _ => rfl, fun _ => ⟨0, ⟨?_, ?_⟩, by simp⟩⟩
    · intro N
      exact ⟨N, le_rfl, by rw [terminal_path M S true p hp hp0 N]; rfl⟩
    · intro c hc hrec
      obtain ⟨n, _, hn⟩ := hrec 0
      rw [terminal_path M S true p hp hp0 n] at hn
      change 0 = c at hn
      omega

private theorem selection_winning {P : Type} (M : UnfoldAutomaton (TransitionAlphabet P))
    (S : TransitionSystem P) (v : S.Vertex) (ρ : Marking M S) :
    Lax369799.ParityWinningRegions.Winning (game M S) true (selection v ρ) ↔
      ∀ q w, S.edge v w → w ∈ ρ q →
        Lax369799.ParityWinningRegions.Winning (game M S) true (position q w) := by
  rw [ParityWinningRegions.predecessor]
  constructor
  · intro h q w hw hρ
    exact h.2 (fun h => h) (position q w) ⟨hw, hρ⟩
  · intro h
    refine ⟨fun h => h.elim, ?_⟩
    intro _ w hw
    rcases w with ⟨q, w⟩ | (⟨w, σ⟩ | b)
    · exact h q w hw.1 hw.2
    · exact hw.elim
    · cases b
      · exact hw.elim
      · exact (terminal_winning M S true).mpr rfl

/--
---
conclusion: Lax369799.ModalAcceptanceGame.winning_equation
---
Collapse each marking choice and its adversarial response. The winning
positions satisfy exactly the positive modal transition equations; the
parity condition determines which fixed point these equations select.
-/
theorem winning_equation {P : Type} (M : UnfoldAutomaton (TransitionAlphabet P))
    (S : TransitionSystem P) (q : Fin M.condition.states) (v : S.Vertex) :
    Lax369799.ParityWinningRegions.Winning (game M S) true (position q v) ↔
      OneStep M q S v (fun p => {w |
        Lax369799.ParityWinningRegions.Winning (game M S) true (position p w)}) := by
  rw [ParityWinningRegions.predecessor]
  constructor
  · intro h
    obtain ⟨w, hw, hwin⟩ := h.1 trivial
    rcases w with ⟨p, w⟩ | (⟨w, ρ⟩ | b)
    · exact hw.elim
    · obtain ⟨rfl, hρ⟩ := hw
      have hb := (selection_winning M S v ρ).mp hwin
      rcases hρ with h | ⟨B, hB, hl, hr⟩
      · exact Or.inl h
      · refine Or.inr ⟨B, hB, ?_, ?_⟩
        · intro b hb'
          obtain ⟨w, hw, hw'⟩ := hl b hb'
          exact ⟨w, hw, hb _ w hw hw'⟩
        · intro w hw
          obtain ⟨b, hb', hw'⟩ := hr w hw
          exact ⟨b, hb', hb _ w hw hw'⟩
    · cases b
      · exact False.elim (Bool.false_ne_true ((terminal_winning M S false).mp hwin))
      · exact hw.elim
  · intro h
    refine ⟨fun _ => ⟨selection v _, ⟨rfl, h⟩,
      (selection_winning M S v _).mpr (fun _ _ _ h => h)⟩, ?_⟩
    intro h
    exact (h trivial).elim

/--
---
conclusion: Lax369799.ModalAcceptanceGame.winning_nested
---
All priorities of the acceptance arena lie below the chosen depth. The
finite parity-game equation theorem therefore identifies its winning
positions with the nested least and greatest fixed points.
-/
theorem winning_nested {P : Type} (M : UnfoldAutomaton (TransitionAlphabet P))
    (S : TransitionSystem P) (q : Fin M.condition.states) (v : S.Vertex) :
    Lax369799.ParityWinningRegions.Winning (game M S) true (position q v) ↔
      position q v ∈ Lax369799.ParityGameEquations.solve (game M S)
        (ceiling M.condition + 1) (fun _ => ∅) := by
  have hbound : ∀ w, (game M S).priority w < ceiling M.condition + 1 := by
    intro w
    rcases w with ⟨q, v⟩ | (⟨v, ρ⟩ | b)
    · change ceiling M.condition - M.condition.priority q < ceiling M.condition + 1
      omega
    · change 0 < ceiling M.condition + 1
      omega
    · cases b
      · change 1 < ceiling M.condition + 1
        unfold ceiling
        omega
      · change 0 < ceiling M.condition + 1
        omega
  rw [← ParityGameEquations.winning (game M S) _ hbound (fun _ => ∅)]
  rfl

end Lax369799Proofs.ModalAcceptanceGame
