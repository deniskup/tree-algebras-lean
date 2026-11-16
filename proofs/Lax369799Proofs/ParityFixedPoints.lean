import Lax369799Proofs.ParityWinningRegions
import Lax369799.ParityFixedPoints

set_option backward.isDefEq.respectTransparency false

namespace Lax369799Proofs.ParityFixedPoints
open Lax369799.FiniteParityGames Lax369799.ParityWinningRegions
open WordAutomata
attribute [local instance] Classical.propDecidable

private def arena {V : Type} (G : Game V) : FinGame.Arena V :=
  ⟨G.eve, G.edge, G.priority⟩

open Lax369799.ParityFixedPoints

theorem parity_shift {V : Type} (G : Game V) (p : ℕ → V) (N : ℕ) :
    G.EveWins (fun n => p (n + N)) ↔ G.EveWins p :=
  (arena G).eveWinsPlay_shift N

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

private theorem after_stop {V : Type} (G : Game V) (C W : Set V) (p : ℕ → V)
    (hp : (stop G C W).IsPlay p) (N : ℕ) (hN : p N ∈ C) :
    ∀ n, p (n + N) = p N := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    have h := hp (n + N)
    change (if p (n + N) ∈ C then p (n + N + 1) = p (n + N) else _) at h
    rw [ih, if_pos hN] at h
    simpa [Nat.succ_add, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h

theorem stopped_parity {V : Type} (G : Game V) (C W : Set V) (p : ℕ → V)
    (hp : (stop G C W).IsPlay p) (N : ℕ) (hN : p N ∈ C) :
    (stop G C W).EveWins p ↔ p N ∈ W := by
  have he : (fun n => p (n + N)) = fun _ => p N := funext (after_stop G C W p hp N hN)
  rw [← parity_shift (stop G C W) p N, he, constant_parity]
  by_cases hW : p N ∈ W <;> simp [stop, hN, hW]

theorem avoids_parity {V : Type} (G : Game V) (C W : Set V) (p : ℕ → V)
    (hp : ∀ n, p n ∉ C) :
    (stop G C W).EveWins p ↔ G.EveWins p := by
  have he : ∀ n, (stop G C W).priority (p n) = G.priority (p n) := fun n => by simp [stop, hp n]
  simp only [Game.EveWins, he]

theorem terminal_winning {V : Type} (G : Game V) (C W : Set V) (player : Bool)
    (v : V) (hv : v ∈ C) :
    Winning (stop G C W) player v ↔ (v ∈ W ↔ player = true) := by
  classical
  constructor
  · rintro ⟨f, hf, hwin⟩
    have hp : (stop G C W).IsPlay (fun _ => v) := fun _ => by simp [stop, hv]
    have hc : (stop G C W).Consistent player f (fun _ => v) := by
      intro n h
      have he := hf v h
      have he' : f v = v := by simpa [stop, hv] using he
      exact he'.symm
    have hh := hwin _ hp rfl hc
    exact (stopped_parity G C W _ hp 0 hv).symm.trans hh
  · intro h
    let f : V → V := fun v => Classical.choose ((stop G C W).total v)
    refine ⟨f, fun v _ => Classical.choose_spec ((stop G C W).total v), ?_⟩
    intro p hp hp0 _
    have hc : p 0 ∈ C := hp0 ▸ hv
    rw [stopped_parity G C W p hp 0 hc, hp0]
    exact h

theorem stop_mono {V : Type} (G : Game V) (C W Z : Set V) (hWZ : W ⊆ Z)
    (v : V) (hv : Winning (stop G C W) true v) : Winning (stop G C Z) true v := by
  classical
  obtain ⟨f, hf, hwin⟩ := hv
  refine ⟨f, hf, ?_⟩
  intro p hp hp0 hc
  have hwp := (hwin p hp hp0 hc).mpr rfl
  refine ⟨fun _ => rfl, fun _ => ?_⟩
  by_cases h : ∃ N, p N ∈ C
  · obtain ⟨N, hN⟩ := h
    exact (stopped_parity G C Z p hp N hN).mpr
      (hWZ ((stopped_parity G C W p hp N hN).mp hwp))
  · have hn : ∀ n, p n ∉ C := fun n hn => h ⟨n, hn⟩
    exact (avoids_parity G C Z p hn).mpr ((avoids_parity G C W p hn).mp hwp)

private theorem phase_terminal {V : Type} (G : Game V) (C : Set V) (player : Bool)
    (X : Set V) (v : V) (hv : v ∈ C) :
    Winning (phase G C player X) player v ↔ v ∈ pre G player X := by
  unfold phase
  rw [terminal_winning G C _ player v hv]
  change ((v ∈ pre G player X ↔ player = true) ↔ player = true) ↔ _
  cases player <;> simp

private theorem region_pre {V : Type} (G : Game V) (player : Bool) :
    Set.Subset (Winning G player) (pre G player (Winning G player)) := by
  rintro v ⟨f, hf, hwin⟩
  refine ⟨?_, ?_⟩
  · intro hv
    exact ⟨f v, hf v hv, f, hf,
      ParityWinningRegions.move G player f v (f v) hwin (hf v hv) (fun _ => rfl)⟩
  · intro hv w he
    exact ⟨f, hf, ParityWinningRegions.move G player f v w hwin he (fun h => (hv h).elim)⟩

theorem phase_region {V : Type} [Finite V] (G : Game V) (C : Set V) (player : Bool) :
    Set.Subset (Winning G player) (Winning (phase G C player (Winning G player)) player) := by
  classical
  let R : Set V := Winning G player
  obtain ⟨f, hf, hwin⟩ := ParityWinningRegions.uniform G player
  let g : V → V := fun v => if v ∈ C then v else f v
  intro v hv
  refine ⟨g, ?_, ?_⟩
  · intro w hw
    by_cases hc : w ∈ C
    · simp [phase, stop, g, hc]
    · simpa [phase, stop, g, hc] using hf w hw
  · intro p hp hp0 hc
    have hR : ∀ n, p n ∈ R := by
      intro n
      induction n with
      | zero => simpa [hp0] using hv
      | succ n ih =>
        have he := hp n
        by_cases hn : p n ∈ C
        · have he' : p (n + 1) = p n := by simpa [phase, stop, hn] using he
          rwa [he']
        · have he' : G.edge (p n) (p (n + 1)) := by simpa [phase, stop, hn] using he
          refine ⟨f, hf, ParityWinningRegions.move G player f _ _ (hwin _ ih) he' ?_⟩
          intro ho
          simpa [g, hn] using hc n ho
    by_cases hhit : ∃ N, p N ∈ C
    · obtain ⟨N, hN⟩ := hhit
      have hpre : p N ∈ pre G player R := region_pre G player (hR N)
      have hh := stopped_parity G C {v | v ∈ pre G player R ↔ player = true} p hp N hN
      change (phase G C player R).EveWins p ↔ (p N ∈ pre G player R ↔ player = true) at hh
      simpa only [hpre, true_iff] using hh
    · have hn : ∀ n, p n ∉ C := fun n hn => hhit ⟨n, hn⟩
      have hpg : G.IsPlay p := fun n => by simpa [phase, stop, hn n] using hp n
      have hcg : G.Consistent player f p := fun n ho => by simpa [g, hn n] using hc n ho
      exact (avoids_parity G C _ p hn).trans (hwin v hv p hpg hp0 hcg)

private theorem path_absorbed {V : Type} (G : Game V) (p : ℕ → V) (hp : G.IsPlay p)
    (N : ℕ) (hN : ∀ w, G.edge (p N) w → w = p N) :
    ∀ n, p (n + N) = p N := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    have h := hp (n + N)
    rw [ih] at h
    have h := hN _ h
    simpa [Nat.succ_add, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h

theorem repeat_phase {V : Type} [Finite V] (G : Game V) (C : Set V) (p : ℕ)
    (hC : ∀ v ∈ C, G.priority v = p)
    (hbound : ∀ v, p < G.priority v → ∀ w, G.edge v w → w = v)
    (player : Bool) (hparity : Even p ↔ player = true) (X : Set V)
    (hX : X ⊆ Winning (phase G C player X) player) : X ⊆ Winning G player := by
  classical
  let R : Set V := Winning (phase G C player X) player
  obtain ⟨f, hf, hwin⟩ := ParityWinningRegions.uniform (phase G C player X) player
  have chooseMove : ∀ v, v ∈ C → v ∈ R → Owned G player v → ∃ w, G.edge v w ∧ w ∈ X := by
    intro v hv hr ho
    exact ((phase_terminal G C player X v hv).mp hr).1 ho
  let d : V → V := fun v => Classical.choose (G.total v)
  have hd : ∀ v, G.edge v (d v) := fun v => Classical.choose_spec (G.total v)
  let g : V → V := fun v => if hv : v ∈ C then
    if hr : v ∈ R ∧ Owned G player v then (chooseMove v hv hr.1 hr.2).choose else d v
    else f v
  have g_cut : ∀ v (hv : v ∈ C) (hr : v ∈ R) (ho : Owned G player v),
      G.edge v (g v) ∧ g v ∈ X := by
    intro v hv hr ho
    simpa only [g, dif_pos hv, dif_pos (show v ∈ R ∧ Owned G player v from ⟨hr, ho⟩)] using
      (chooseMove v hv hr ho).choose_spec
  have g_away : ∀ v, v ∉ C → g v = f v := by
    intro v hv
    simp only [g, dif_neg hv]
  have hg : G.Legal player g := by
    intro v ho
    by_cases hv : v ∈ C
    · by_cases hr : v ∈ R
      · exact (g_cut v hv hr ho).1
      · simpa only [g, dif_pos hv, dif_neg (show ¬ (v ∈ R ∧ Owned G player v) from
          fun h => hr h.1)] using hd v
    · rw [g_away v hv]
      simpa [phase, stop, hv] using hf v ho
  have hgR : ∀ v ∈ R, ∀ w, G.edge v w → (Owned G player v → w = g v) → w ∈ R := by
    intro v hv w he hc
    by_cases hcut : v ∈ C
    · have hpre := (phase_terminal G C player X v hcut).mp hv
      by_cases ho : Owned G player v
      · rw [hc ho]
        exact hX (g_cut v hcut hv ho).2
      · exact hX (hpre.2 ho w he)
    · refine ⟨f, hf, ParityWinningRegions.move (phase G C player X) player f v w
        (hwin v hv) (by simpa [phase, stop, hcut] using he) ?_⟩
      intro ho
      rw [hc ho, g_away v hcut]
  intro v hv
  refine ⟨g, hg, ?_⟩
  intro π hπ hπ0 hc
  have hR : ∀ n, π n ∈ R := by
    intro n
    induction n with
    | zero => simpa [hπ0] using hX hv
    | succ n ih => exact hgR (π n) ih (π (n + 1)) (hπ n) (hc n)
  by_cases hfreq : ∀ N, ∃ n, N ≤ n ∧ π n ∈ C
  · have hle : ∀ n, G.priority (π n) ≤ p := by
      intro n
      by_contra hh
      have hhigh : p < G.priority (π n) := by omega
      have hstay := path_absorbed G π hπ n (hbound (π n) hhigh)
      obtain ⟨m, hm, hmC⟩ := hfreq n
      have he : π m = π n := by simpa [Nat.sub_add_cancel hm] using hstay (m - n)
      have hp := hC (π m) hmC
      rw [he] at hp
      omega
    have hr : ∀ N, ∃ n, N ≤ n ∧ G.priority (π n) = p := by
      intro N
      obtain ⟨n, hn, hnC⟩ := hfreq N
      exact ⟨n, hn, hC _ hnC⟩
    have hmax : ∀ c, p < c → ¬ ∀ N, ∃ n, N ≤ n ∧ G.priority (π n) = c := by
      intro c hc hrec
      obtain ⟨n, _, hn⟩ := hrec 0
      have := hle n
      omega
    constructor
    · rintro ⟨c, ⟨hcrec, hcmax⟩, heven⟩
      have heq : c = p := by
        obtain ⟨n, _, hn⟩ := hcrec 0
        have := hle n
        by_contra hcp
        have hcp : c < p := by omega
        exact hcmax p hcp hr
      exact hparity.mp (heq ▸ heven)
    · intro hplayer
      exact ⟨p, ⟨hr, hmax⟩, hparity.mpr hplayer⟩
  · push Not at hfreq
    obtain ⟨N, hN⟩ := hfreq
    let τ := fun n => π (n + N)
    have hcut : ∀ n, τ n ∉ C := fun n => hN (n + N) (by omega)
    have ht : (phase G C player X).IsPlay τ := by
      intro n
      change (if τ n ∈ C then τ (n + 1) = τ n else G.edge (τ n) (τ (n + 1)))
      rw [if_neg (hcut n)]
      simpa [τ, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hπ (n + N)
    have hct : (phase G C player X).Consistent player f τ := by
      intro n ho
      have he := hc (n + N) ho
      rw [g_away _ (hcut n)] at he
      simpa [τ, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using he
    have htwin := hwin (π N) (hR N) τ ht (by simp [τ]) hct
    exact (parity_shift G π N).symm.trans ((avoids_parity G C _ τ hcut).symm.trans htwin)

private theorem pre_mono {V : Type} (G : Game V) (player : Bool) {X Y : Set V}
    (h : X ⊆ Y) : pre G player X ⊆ pre G player Y := by
  rintro v ⟨he, ha⟩
  refine ⟨?_, fun ho w hw => h (ha ho w hw)⟩
  intro ho
  obtain ⟨w, hw, hX⟩ := he ho
  exact ⟨w, hw, h hX⟩

noncomputable def phaseMap {V : Type} (G : Game V) (C : Set V) : Set V →o Set V where
  toFun := fun X => Winning (phase G C true X) true
  monotone' := by
    intro X Y h v hv
    apply stop_mono G C _ _ _ v hv
    intro w hw
    exact ⟨fun _ => rfl, fun _ => pre_mono G true h (hw.mpr rfl)⟩

private theorem pre_complement {V : Type} (G : Game V) (X : Set V) (v : V) :
    v ∈ pre G false Xᶜ ↔ v ∉ pre G true X := by
  classical
  by_cases hv : G.eve v
  · simp [pre, Owned, hv, Set.mem_compl_iff, not_exists, not_and]
  · simp [pre, Owned, hv, Set.mem_compl_iff, not_forall]

private theorem phase_complement {V : Type} (G : Game V) (C X : Set V) :
    phase G C false Xᶜ = phase G C true X := by
  unfold phase
  congr 1
  ext v
  change ((v ∈ pre G false Xᶜ ↔ false = true) ↔ (v ∈ pre G true X ↔ true = true))
  rw [pre_complement]
  simp

private theorem phase_fixed {V : Type} [Finite V] (G : Game V) (C : Set V) :
    phaseMap G C (Winning G true) = Winning G true := by
  classical
  apply Set.Subset.antisymm
  · intro v hv
    by_contra hn
    have ha := (ParityWinningRegions.complementary G v).mpr hn
    have heq : (Winning G false : Set V) = (Winning G true : Set V)ᶜ := by
      ext w
      exact ParityWinningRegions.complementary G w
    have hh := phase_region G C false ha
    rw [heq] at hh
    change Winning (phase G C false (Winning G true : Set V)ᶜ) false v at hh
    rw [phase_complement] at hh
    exact ParityWinningRegions.disjoint (phase G C true (Winning G true)) v ⟨hv, hh⟩
  · exact phase_region G C true

/--
---
conclusion: Lax369799.ParityFixedPoints.greatest
---
Repeated phases either visit priority p infinitely often, which is winning when p is even, or eventually remain in a single winning stopped phase. This proves maximality of the winning fixed point.
-/
theorem greatest {V : Type} [Finite V] (G : Game V) (C : Set V) (p : ℕ)
    (hC : ∀ v ∈ C, G.priority v = p)
    (hbound : ∀ v, p < G.priority v → ∀ w, G.edge v w → w = v)
    (hp : Even p) : (Winning G true : Set V) = (sSup {X : Set V | X ⊆ Winning (phase G C true X) true} : Set V) := by
  change (Winning G true : Set V) = (phaseMap G C).gfp
  apply Set.Subset.antisymm
  · exact (phaseMap G C).le_gfp (by rw [phase_fixed])
  · apply (phaseMap G C).gfp_le
    intro X hX
    exact repeat_phase G C p hC hbound true ⟨fun _ => rfl, fun _ => hp⟩ X hX

/--
---
conclusion: Lax369799.ParityFixedPoints.least
---
Apply the repeated-phase argument to Adam on the complement of each prefixed point. Odd recurrent priority is winning for Adam, forcing Eve’s region into every prefixed point.
-/
theorem least {V : Type} [Finite V] (G : Game V) (C : Set V) (p : ℕ)
    (hC : ∀ v ∈ C, G.priority v = p)
    (hbound : ∀ v, p < G.priority v → ∀ w, G.edge v w → w = v)
    (hp : ¬ Even p) : (Winning G true : Set V) = (sInf {X : Set V | Set.Subset (Winning (phase G C true X) true) X} : Set V) := by
  change (Winning G true : Set V) = (phaseMap G C).lfp
  classical
  apply Set.Subset.antisymm
  · apply (phaseMap G C).le_lfp
    intro X hX v hv
    by_contra hn
    have hnot : Xᶜ ⊆ Winning (phase G C false Xᶜ) false := by
      intro w hw
      rw [phase_complement]
      change Winning (phase G C true X) false w
      apply (ParityWinningRegions.complementary _ w).mpr
      exact fun h => hw (hX h)
    have ha := repeat_phase G C p hC hbound false
      ⟨fun h => (hp h).elim, fun h => (Bool.false_ne_true h).elim⟩ Xᶜ hnot hn
    exact ParityWinningRegions.disjoint G v ⟨hv, ha⟩
  · exact (phaseMap G C).lfp_le (by rw [phase_fixed])

end Lax369799Proofs.ParityFixedPoints
