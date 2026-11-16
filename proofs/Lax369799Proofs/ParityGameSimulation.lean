import Lax369799.ParityGameSimulation
import Lax369799Proofs.ParityWinningRegions
import Lax369799Proofs.FiniteParityGames

set_option backward.isDefEq.respectTransparency false
namespace Lax369799Proofs.ParityGameSimulation
open Lax369799
open FiniteParityGames ParityWinningRegions Lax369799.ParityGameSimulation

/--
---
conclusion: Lax369799.ParityGameSimulation.winning
---
Pair the source winning strategy with a putative target counterstrategy.
The simulation lifts moves according to their owner. The resulting plays
have identical priorities, contradicting their opposite winners.
-/
theorem winning {V W : Type} [Finite W] (G : Game V) (H : Game W) (R : V → W → Prop)
    (s : Simulation G H R) (v : V) (w : W) (hR : R v w)
    (h : Winning G true v) : Winning H true w := by
  classical
  obtain ⟨f,hf,hw⟩ := h
  obtain ⟨a,g,ha,hg,hd⟩ := FiniteParityGames.positional_determinacy H
  rcases hd w with hyes | hno
  · exact ⟨a,ha,hyes⟩
  let X := {p : V × W // R p.1 p.2}
  let Step (x y : X) : Prop :=
    G.edge x.val.1 y.val.1 ∧ H.edge x.val.2 y.val.2 ∧
      (G.eve x.val.1 → y.val.1 = f x.val.1) ∧
      (¬G.eve x.val.1 → y.val.2 = g x.val.2)
  have ex (x : X) : ∃ y,Step x y := by
    by_cases he : G.eve x.val.1
    · have he' := hf x.val.1 (by simp [he])
      obtain ⟨w',ht,hr⟩ := s.eve_step _ _ x.property he _ he'
      exact ⟨⟨(f x.val.1,w'),hr⟩,he',ht,(fun _ => rfl),(fun hn => (hn he).elim)⟩
    · have he' := hg x.val.2 (by
        have hn : ¬H.eve x.val.2 := fun h => he ((s.owner _ _ x.property).mpr h)
        simp [hn])
      obtain ⟨v',ht,hr⟩ := s.adam_step _ _ x.property he _ he'
      exact ⟨⟨(v',g x.val.2),hr⟩,ht,he',(fun hh => (he hh).elim),(fun _ => rfl)⟩
  let st : ℕ → X := fun n => Nat.rec ⟨(v,w),hR⟩ (fun _ x => (ex x).choose) n
  have hst (n : ℕ) : Step (st n) (st (n+1)) := (ex (st n)).choose_spec
  let p := fun n => (st n).val.1
  let q := fun n => (st n).val.2
  have hgp : G.IsPlay p := fun n => (hst n).1
  have hhq : H.IsPlay q := fun n => (hst n).2.1
  have hfc : G.Consistent true f p := by
    intro n hn
    exact (hst n).2.2.1 (hn.mpr rfl)
  have hgc : H.Consistent false g q := by
    intro n hn
    apply (hst n).2.2.2
    intro he
    have hh := (s.owner _ _ (st n).property).mp he
    exact Bool.false_ne_true (hn.mp hh)
  have hpar : G.EveWins p := (hw p hgp rfl hfc).mpr rfl
  have hpq (n : ℕ) : H.priority (q n) = G.priority (p n) := (s.priority _ _ (st n).property).symm
  have hpar' : H.EveWins q := by
    unfold Game.EveWins
    simp_rw [hpq]
    exact hpar
  exact (Bool.false_ne_true ((hno q hhq rfl hgc).mp hpar')).elim

end Lax369799Proofs.ParityGameSimulation
