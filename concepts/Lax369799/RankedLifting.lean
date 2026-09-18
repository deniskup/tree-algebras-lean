import Lax369799.BisimulationQuotient
import Lax369799.TransitionEncoding

/-!
---
title: Ranking a functional bisimulation
type: theorem
---
A functional bisimulation between finite transition systems can be
represented by a ranked system morphism. Directions enumerate target
successors with enough repeated copies to cover every source successor.
Forgetting the directions recovers the original transition systems.
-/
namespace Lax369799.RankedLifting
open RankedSystems Morphisms TransitionSystems TransitionEncoding BisimulationQuotient

axiom map_lift {P : Type} (S T : TransitionSystem P) (f : SystemMap S T) :
    ∃ (R U : System (TransitionAlphabet P) 0), decode R = S ∧ decode U = T ∧
      Nonempty (Morphism R.val U.val)

end Lax369799.RankedLifting
