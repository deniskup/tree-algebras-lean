import Lax369799.ParityWinningRegions

/-!
---
title: Transfer of winning through alternating game simulation
type: theorem
---
The simulation preserves owners and priorities, matching Eve's source
choices and lifting Adam's target choices. Finite target determinacy
then transfers a source winning strategy.
-/

namespace Lax369799.ParityGameSimulation
open FiniteParityGames

structure Simulation {V W : Type} (G : Game V) (H : Game W) (R : V → W → Prop) where
  owner : ∀ v w,R v w → (G.eve v ↔ H.eve w)
  priority : ∀ v w,R v w → G.priority v = H.priority w
  eve_step : ∀ v w,R v w → G.eve v → ∀ v',G.edge v v' → ∃ w',H.edge w w' ∧ R v' w'
  adam_step : ∀ v w,R v w → ¬G.eve v → ∀ w',H.edge w w' → ∃ v',G.edge v v' ∧ R v' w'

open ParityWinningRegions

axiom winning {V W : Type} [Finite W] (G : Game V) (H : Game W) (R : V → W → Prop)
    (s : Simulation G H R) (v : V) (w : W) (hR : R v w)
    (h : Winning G true v) : Winning H true w

end Lax369799.ParityGameSimulation