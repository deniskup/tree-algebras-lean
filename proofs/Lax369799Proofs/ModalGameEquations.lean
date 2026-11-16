import Lax369799.ModalGameEquations
import Lax369799Proofs.ModalAcceptanceGame
import Lax369799Proofs.FixedPointRetraction

set_option backward.isDefEq.respectTransparency false

namespace Lax369799Proofs.ModalGameEquations
open Lax369799
open TransitionSystems TransitionEncoding UnfoldAutomata ModalTransitions ModalAcceptanceGame
open FiniteParityGames ParityWinningRegions ParityFixedPoints
attribute [local instance] Classical.propDecidable

open Lax369799.ModalGameEquations

private theorem project_lift {P : Type} (M : UnfoldAutomaton (TransitionAlphabet P))
    (S : TransitionSystem P) (X : Marking M S) : project M S (lift M S X) = X := rfl

private def Auxiliary {P : Type} (M : UnfoldAutomaton (TransitionAlphabet P))
    (S : TransitionSystem P) (G : Game (Vertex M S)) : Prop :=
  ∀ t, (∀ q v, t ≠ position q v) →
    G.eve t = (game M S).eve t ∧ G.edge t = (game M S).edge t ∧
      G.priority t = (game M S).priority t

private theorem auxiliary_stop {P : Type} (M : UnfoldAutomaton (TransitionAlphabet P))
    (S : TransitionSystem P) (G : Game (Vertex M S)) (hG : Auxiliary M S G)
    (B : Fin M.condition.states → S.Vertex → Prop) (W : Set (Vertex M S)) :
    Auxiliary M S (stop G (boundary M S B) W) := by
  intro t ht
  have hnot : t ∉ boundary M S B := by
    rcases t with ⟨q, v⟩ | (⟨v, ρ⟩ | b)
    · exact (ht q v rfl).elim
    · exact id
    · exact id
  simpa only [stop, if_neg hnot] using hG t ht

private theorem constant_parity {V : Type} (G : Game V) (v : V) :
    G.EveWins (fun _ => v) ↔ Even (G.priority v) := by
  constructor
  · rintro ⟨c, ⟨hr, _⟩, hc⟩
    obtain ⟨n, _, hn⟩ := hr 0
    rwa [← hn] at hc
  · intro h
    refine ⟨G.priority v, ⟨fun N => ⟨N, le_rfl, rfl⟩, ?_⟩, h⟩
    intro c hc hr
    obtain ⟨n, _, hn⟩ := hr 0
    change G.priority v = c at hn
    omega

private theorem absorbing {V : Type} (G : Game V) (v : V)
    (hv : ∀ w, G.edge v w ↔ w = v) : Winning G true v ↔ Even (G.priority v) := by
  classical
  constructor
  · rintro ⟨f, hf, hw⟩
    apply (constant_parity G v).mp
    exact (hw (fun _ => v) (fun _ => (hv v).mpr rfl) rfl
      (fun n ho => ((hv (f v)).mp (hf v ho)).symm)).mpr rfl
  · intro he
    let f : V → V := fun v => Classical.choose (G.total v)
    refine ⟨f, fun v _ => Classical.choose_spec (G.total v), ?_⟩
    intro p hp hp0 _
    have h : ∀ n, p n = v := by
      intro n
      induction n with
      | zero => exact hp0
      | succ n ih =>
        have hh := hp n
        rw [ih] at hh
        exact (hv _).mp hh
    have hp' : p = fun _ => v := funext h
    rw [hp', constant_parity]
    exact ⟨fun _ => rfl, fun _ => he⟩

private theorem terminal_winning {P : Type} (M : UnfoldAutomaton (TransitionAlphabet P))
    (S : TransitionSystem P) (G : Game (Vertex M S)) (hG : Auxiliary M S G) (b : Bool) :
    Winning G true (terminal b) ↔ b = true := by
  have h := hG (terminal b) (by intro q v he; cases he)
  rw [absorbing G (terminal b) (by
    intro w
    rw [h.2.1]
    rcases w with ⟨q, v⟩ | (⟨v, ρ⟩ | c)
    · simp [game, Edge, terminal]
    · simp [game, Edge, terminal]
    · simp [game, Edge, terminal, eq_comm]), h.2.2]
  cases b <;> simp [game, priority, terminal]

private theorem winning_lift {P : Type} (M : UnfoldAutomaton (TransitionAlphabet P))
    (S : TransitionSystem P) (G : Game (Vertex M S)) (hG : Auxiliary M S G) :
    lift M S (project M S (Winning G true)) = Winning G true := by
  ext t
  rcases t with ⟨q, v⟩ | (⟨v, ρ⟩ | b)
  · rfl
  · have h := hG (selection v ρ) (by intro q w he; cases he)
    change (∀ q w, S.edge v w → w ∈ ρ q → Winning G true (position q w)) ↔ Winning G true (selection v ρ)
    rw [ParityWinningRegions.predecessor]
    constructor
    · intro hwin
      refine ⟨?_, ?_⟩
      · intro he
        rw [h.1] at he
        exact he.elim
      · intro _ w hw
        rw [h.2.1] at hw
        rcases w with ⟨q, w⟩ | (⟨w, σ⟩ | b)
        · exact hwin q w hw.1 hw.2
        · exact hw.elim
        · cases b
          · exact hw.elim
          · exact (terminal_winning M S G hG true).mpr rfl
    · intro hwin q w hw hρ
      apply hwin.2 (by rw [h.1]; exact id) (position q w)
      rw [h.2.1]
      exact ⟨hw, hρ⟩
  · exact (terminal_winning M S G hG b).symm

private theorem pre_lift {P : Type} (M : UnfoldAutomaton (TransitionAlphabet P))
    (S : TransitionSystem P) (q : Fin M.condition.states) (v : S.Vertex) (X : Marking M S) :
    position q v ∈ pre (game M S) true (lift M S X) ↔ OneStep M q S v X := by
  constructor
  · intro h
    obtain ⟨w, hw, hx⟩ := h.1 ⟨fun _ => rfl, fun _ => trivial⟩
    rcases w with ⟨p, w⟩ | (⟨w, ρ⟩ | b)
    · exact hw.elim
    · obtain ⟨rfl, hρ⟩ := hw
      rcases hρ with h | ⟨B, hB, hl, hr⟩
      · exact Or.inl h
      · refine Or.inr ⟨B, hB, ?_, ?_⟩
        · intro b hb
          obtain ⟨w, hw, hw'⟩ := hl b hb
          exact ⟨w, hw, hx _ w hw hw'⟩
        · intro w hw
          obtain ⟨b, hb, hw'⟩ := hr w hw
          exact ⟨b, hb, hx _ w hw hw'⟩
    · cases b
      · exact Bool.false_ne_true hx |>.elim
      · exact hw.elim
  · intro h
    refine ⟨fun _ => ⟨selection v X, ⟨rfl, h⟩, fun _ _ _ h => h⟩, ?_⟩
    intro h
    exact (h ⟨fun _ => rfl, fun _ => trivial⟩).elim

private theorem game_ext {V : Type} {G H : Game V}
    (ho : G.eve = H.eve) (he : G.edge = H.edge) (hp : G.priority = H.priority) : G = H := by
  cases G; cases H; cases ho; cases he; cases hp; rfl

private theorem stopped_phase {P : Type} (M : UnfoldAutomaton (TransitionAlphabet P))
    (S : TransitionSystem P) (n : ℕ) (ρ : ℕ → Marking M S) (X : Marking M S) :
    phase (stopped M S (n + 1) ρ) (boundary M S (fun q _ => statePriority M q = n))
        true (lift M S X) = stopped M S n (Function.update ρ n X) := by
  classical
  apply game_ext
  · rfl
  · funext t w
    rcases t with ⟨q, v⟩ | (⟨v, σ⟩ | b)
    · rcases lt_trichotomy (statePriority M q) n with h | h | h
      · simp [phase, stopped, stop, Set.mem_ofPred_eq, boundary, show ¬ n ≤ statePriority M q by omega,
          show ¬ n < statePriority M q by omega, show statePriority M q ≠ n by omega]
      · simp [phase, stopped, stop, Set.mem_ofPred_eq, boundary, h]
      · simp [phase, stopped, stop, Set.mem_ofPred_eq, boundary, show n ≤ statePriority M q by omega,
          show n < statePriority M q by omega, show statePriority M q ≠ n by omega]
    · simp [phase, stopped, stop, Set.mem_ofPred_eq, boundary]
    · simp [phase, stopped, stop, Set.mem_ofPred_eq, boundary]
  · funext t
    rcases t with ⟨q, v⟩ | (⟨v, σ⟩ | b)
    · rcases lt_trichotomy (statePriority M q) n with h | h | h
      · simp [phase, stopped, stop, Set.mem_ofPred_eq, boundary, show ¬ n ≤ statePriority M q by omega,
          show ¬ n < statePriority M q by omega, show statePriority M q ≠ n by omega]
      · have hb : ¬ n + 1 ≤ statePriority M q := by omega
        have hp : position q v ∈ pre (stopped M S (n + 1) ρ) true (lift M S X) ↔
            OneStep M q S v X := by
          convert pre_lift M S q v X using 1
          simp only [pre, Owned, stopped, stop, Set.mem_ofPred_eq, boundary, position, if_neg hb]
        simp only [phase, stop, boundary, Set.mem_ofPred_eq, h, if_true, iff_true]
        simp only [position] at hp
        rw [hp]
        simp [stopped, stop, boundary, h]
      · simp [phase, stopped, stop, Set.mem_ofPred_eq, boundary, show n ≤ statePriority M q by omega,
          show n < statePriority M q by omega, show statePriority M q ≠ n by omega]
    · simp [phase, stopped, stop, Set.mem_ofPred_eq, boundary]
    · simp [phase, stopped, stop, Set.mem_ofPred_eq, boundary]

/--
---
conclusion: Lax369799.ModalGameEquations.solve_stopped
---
Induct on the cutoff, projecting each least or greatest fixed point through the marking-position retraction.
-/
theorem solve_stopped {P : Type} (M : UnfoldAutomaton (TransitionAlphabet P))
    (S : TransitionSystem P) (n : ℕ) (ρ : ℕ → Marking M S) :
    project M S (Winning (stopped M S n ρ) true) = solve M S n ρ := by
  classical
  induction n generalizing ρ with
  | zero =>
    funext q
    ext v
    exact (ParityFixedPoints.terminal_winning (game M S) _ _ true (position q v)
      (Nat.zero_le _)).trans (by simp only [iff_true]; rfl)
  | succ n ih =>
    let G := stopped M S (n + 1) ρ
    let C := boundary M S (fun q _ => statePriority M q = n)
    let F := ParityFixedPoints.phaseMap G C
    have haux : Auxiliary M S G := auxiliary_stop M S (game M S)
      (by intro t ht; exact ⟨rfl, rfl, rfl⟩) _ _
    have hC : ∀ t ∈ C, G.priority t = n := by
      intro t ht
      rcases t with ⟨q, v⟩ | (⟨v, σ⟩ | b)
      · change statePriority M q = n at ht
        dsimp only [G, stopped, stop, Set.mem_ofPred_eq, boundary]
        rw [if_neg (show ¬ n + 1 ≤ statePriority M q by omega)]
        exact ht
      · exact ht.elim
      · exact ht.elim
    have hbound : ∀ t, n < G.priority t → ∀ w, G.edge t w → w = t := by
      intro t ht w hw
      rcases t with ⟨q, v⟩ | (⟨v, σ⟩ | b)
      · by_cases h : n + 1 ≤ statePriority M q
        · simpa only [G, stopped, stop, Set.mem_ofPred_eq, boundary, if_pos h] using hw
        · dsimp only [G, stopped, stop, Set.mem_ofPred_eq, boundary] at ht
          rw [if_neg h] at ht
          change n < statePriority M q at ht
          omega
      · simp only [G, stopped, stop, Set.mem_ofPred_eq, boundary, if_false] at ht
        change n < 0 at ht
        omega
      · simp only [G, stopped, stop, Set.mem_ofPred_eq, boundary, if_false] at hw
        change (game M S).edge (terminal b) w at hw
        rcases w with ⟨q, v⟩ | (⟨v, σ⟩ | c)
        · exact hw.elim
        · exact hw.elim
        · exact congrArg terminal hw.symm
    have hF : ∀ X, lift M S (project M S (F X)) = F X := by
      intro X
      exact winning_lift M S (phase G C true X) (auxiliary_stop M S G haux _ _)
    let H := Lax369799.FixedPointRetraction.reduced F (project M S) (lift M S)
    have hH : ∀ X, H X = solve M S n (Function.update ρ n X) := by
      intro X
      change project M S (Winning (phase (stopped M S (n + 1) ρ) C true (lift M S X)) true) = _
      rw [show C = boundary M S (fun q _ => statePriority M q = n) from rfl, stopped_phase]
      exact ih _
    by_cases hp : Even n
    · have he := ParityFixedPoints.greatest G C n hC hbound hp
      change (Winning G true : Set (Vertex M S)) = F.gfp at he
      have h := (congrArg (project M S) he).trans
        (FixedPointRetraction.greatest F (project M S) (lift M S) (project_lift M S) hF)
      change project M S (Winning G true) = (sSup {X : Marking M S | X ≤ H X}) at h
      simpa only [solve, if_pos hp, hH] using h
    · have he := ParityFixedPoints.least G C n hC hbound hp
      change (Winning G true : Set (Vertex M S)) = F.lfp at he
      have h := (congrArg (project M S) he).trans
        (FixedPointRetraction.least F (project M S) (lift M S) (project_lift M S) hF)
      change project M S (Winning G true) = (sInf {X : Marking M S | H X ≤ X}) at h
      simpa only [solve, if_neg hp, hH] using h

/--
---
conclusion: Lax369799.ModalGameEquations.winning
---
Once every word-state priority lies below the cutoff, no position is stopped. The projected equations then give the original winning region.
-/
theorem winning {P : Type} (M : UnfoldAutomaton (TransitionAlphabet P))
    (S : TransitionSystem P) (n : ℕ) (hn : ∀ q, statePriority M q < n)
    (ρ : ℕ → Marking M S) :
    project M S (Winning (game M S) true) = solve M S n ρ := by
  classical
  have he : stopped M S n ρ = game M S := by
    apply game_ext
    · rfl
    · funext t w
      rcases t with ⟨q, v⟩ | (⟨v, σ⟩ | b)
      · simp [stopped, stop, Set.mem_ofPred_eq, boundary, show ¬ n ≤ statePriority M q from Nat.not_le.mpr (hn q)]
      · simp [stopped, stop, Set.mem_ofPred_eq, boundary]
      · simp [stopped, stop, Set.mem_ofPred_eq, boundary]
    · funext t
      rcases t with ⟨q, v⟩ | (⟨v, σ⟩ | b)
      · simp [stopped, stop, Set.mem_ofPred_eq, boundary, show ¬ n ≤ statePriority M q from Nat.not_le.mpr (hn q)]
      · simp [stopped, stop, Set.mem_ofPred_eq, boundary]
      · simp [stopped, stop, Set.mem_ofPred_eq, boundary]
  have h := solve_stopped M S n ρ
  rwa [he] at h

end Lax369799Proofs.ModalGameEquations
