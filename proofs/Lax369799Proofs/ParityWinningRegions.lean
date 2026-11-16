import Lax369799.ParityWinningRegions
import Lax369799Proofs.FiniteParityGames

namespace Lax369799Proofs.ParityWinningRegions
open Lax369799.FiniteParityGames Lax369799.ParityWinningRegions
open WordAutomata

private def arena {V : Type} (G : Game V) : FinGame.Arena V :=
  ⟨G.eve, G.edge, G.priority⟩

private theorem winsE {V : Type} (G : Game V) (f : V → V) (v : V) :
    G.WinsFrom true f v ↔ (arena G).WinsE Set.univ f v := by
  constructor
  · intro h p hp hp0 hc
    exact (h p hp.1 hp0 (fun n hn => hc n (hn.mpr rfl))).mpr rfl
  · intro h p hp hp0 hc
    exact ⟨fun _ => rfl, fun _ => h p ⟨hp, fun _ => trivial⟩ hp0
      (fun n hn => hc n ⟨fun _ => rfl, fun _ => hn⟩)⟩

private theorem winsA {V : Type} (G : Game V) (f : V → V) (v : V) :
    G.WinsFrom false f v ↔ (arena G).WinsA Set.univ f v := by
  constructor
  · intro h p hp hp0 hc hw
    exact Bool.false_ne_true ((h p hp.1 hp0 (fun n hn =>
      hc n (fun he => Bool.false_ne_true (hn.mp he)))).mp hw)
  · intro h p hp hp0 hc
    have hnot := h p ⟨hp, fun _ => trivial⟩ hp0
      (fun n hn => hc n ⟨fun he => (hn he).elim, fun he => (Bool.false_ne_true he).elim⟩)
    exact ⟨fun he => (hnot he).elim, fun he => (Bool.false_ne_true he).elim⟩

private theorem eveOK {V : Type} (G : Game V) (f : V → V) (hf : G.Legal true f) :
    (arena G).EveOK Set.univ f := fun v _ hv =>
  ⟨trivial, hf v ⟨fun _ => rfl, fun _ => hv⟩⟩

private theorem adamOK {V : Type} (G : Game V) (f : V → V) (hf : G.Legal false f) :
    (arena G).AdamOK Set.univ f := fun v _ hv =>
  ⟨trivial, hf v ⟨fun he => (hv he).elim, fun he => (Bool.false_ne_true he).elim⟩⟩

/--
---
conclusion: Lax369799.ParityWinningRegions.move
---
Prepend the given move to any consistent continuation. Removing that
finite prefix leaves the parity of the recurrent priorities unchanged.
-/
theorem move {V : Type} (G : Game V) (player : Bool) (f : V → V) (v w : V)
    (hv : G.WinsFrom player f v) (he : G.edge v w)
    (hf : (G.eve v ↔ player = true) → w = f v) : G.WinsFrom player f w := by
  cases player
  · apply (winsA G f w).mpr
    exact FinGame.Arena.winsA_step (arena G) ((winsA G f v).mp hv) trivial he
      (fun h => hf ⟨fun he => (h he).elim, fun he => (Bool.false_ne_true he).elim⟩)
  · apply (winsE G f w).mpr
    exact FinGame.Arena.winsE_step (arena G) ((winsE G f v).mp hv) trivial he
      (fun h => hf ⟨fun _ => rfl, fun _ => h⟩)

/--
---
conclusion: Lax369799.ParityWinningRegions.disjoint
---
The play following both alleged winning strategies would have to satisfy
both parity outcomes.
-/
theorem disjoint {V : Type} (G : Game V) (v : V) :
    ¬ (Winning G true v ∧ Winning G false v) := by
  rintro ⟨⟨f, hf, hfv⟩, ⟨g, hg, hgv⟩⟩
  exact FinGame.Arena.not_winsE_winsA (a := arena G) (Set.mem_univ v)
    (eveOK G f hf) (adamOK G g hg) ((winsE G f v).mp hfv) ((winsA G g v).mp hgv)

/--
---
conclusion: Lax369799.ParityWinningRegions.uniform
---
The strategies supplied by finite positional determinacy win throughout
their respective regions, since opposite winning claims are disjoint.
-/
theorem uniform {V : Type} [Finite V] (G : Game V) (player : Bool) :
    ∃ f, G.Legal player f ∧ ∀ v, Winning G player v → G.WinsFrom player f v := by
  obtain ⟨f, g, hf, hg, hfg⟩ := FiniteParityGames.positional_determinacy G
  cases player
  · refine ⟨g, hg, fun v hv => ?_⟩
    rcases hfg v with h | h
    · exact (disjoint G v ⟨⟨f, hf, h⟩, hv⟩).elim
    · exact h
  · refine ⟨f, hf, fun v hv => ?_⟩
    rcases hfg v with h | h
    · exact h
    · exact (disjoint G v ⟨hv, ⟨g, hg, h⟩⟩).elim

/--
---
conclusion: Lax369799.ParityWinningRegions.complementary
---
Disjointness and positional determinacy give the partition into the two
winning regions.
-/
theorem complementary {V : Type} [Finite V] (G : Game V) (v : V) :
    Winning G false v ↔ ¬ Winning G true v := by
  constructor
  · exact fun h h' => disjoint G v ⟨h', h⟩
  · intro h
    obtain ⟨f, g, hf, hg, hfg⟩ := FiniteParityGames.positional_determinacy G
    rcases hfg v with h' | h'
    · exact (h ⟨f, hf, h'⟩).elim
    · exact ⟨g, hg, h'⟩

/--
---
conclusion: Lax369799.ParityWinningRegions.predecessor
---
A winning strategy supplies a winning successor at Eve's vertices and
keeps every successor winning at Adam's vertices. For the converse,
an opposing winning strategy would contradict these successor conditions.
-/
theorem predecessor {V : Type} [Finite V] (G : Game V) (v : V) :
    Winning G true v ↔ v ∈ Pre G (Winning G true) := by
  constructor
  · rintro ⟨f, hf, hv⟩
    refine ⟨?_, ?_⟩
    · intro heve
      have he := hf v ⟨fun _ => rfl, fun _ => heve⟩
      exact ⟨f v, he, f, hf, move G true f v (f v) hv he (fun _ => rfl)⟩
    · intro hadam w he
      exact ⟨f, hf, move G true f v w hv he (fun h => (hadam (h.mpr rfl)).elim)⟩
  · intro hpre
    by_contra hv
    obtain ⟨g, hg, hgv⟩ := (complementary G v).mpr hv
    by_cases heve : G.eve v
    · obtain ⟨w, he, hw⟩ := hpre.1 heve
      have hw' := move G false g v w hgv he
        (fun h => (Bool.false_ne_true (h.mp heve)).elim)
      exact disjoint G w ⟨hw, ⟨g, hg, hw'⟩⟩
    · have he := hg v ⟨fun h => (heve h).elim, fun h => (Bool.false_ne_true h).elim⟩
      have hw := hpre.2 heve (g v) he
      exact disjoint G (g v) ⟨hw, ⟨g, hg, move G false g v (g v) hgv he (fun _ => rfl)⟩⟩

end Lax369799Proofs.ParityWinningRegions
