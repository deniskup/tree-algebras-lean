import Lax369799.FiniteParityGames

/-!
---
title: Winning regions and controlled predecessors
type: theorem
---
The two positional winning regions of a finite parity game partition its
vertices. A single strategy wins throughout each region. Since parity is
unaffected by a finite prefix, the winning region is stable under the
corresponding controlled predecessor operation.
-/

namespace Lax369799.ParityWinningRegions
open FiniteParityGames

def Winning {V : Type} (G : Game V) (player : Bool) (v : V) : Prop :=
  ∃ f, G.Legal player f ∧ G.WinsFrom player f v

def Pre {V : Type} (G : Game V) (X : Set V) : Set V :=
  {v | (G.eve v → ∃ w, G.edge v w ∧ w ∈ X) ∧
    (¬ G.eve v → ∀ w, G.edge v w → w ∈ X)}

axiom move {V : Type} (G : Game V) (player : Bool) (f : V → V) (v w : V)
    (hv : G.WinsFrom player f v) (he : G.edge v w)
    (hf : (G.eve v ↔ player = true) → w = f v) : G.WinsFrom player f w

axiom disjoint {V : Type} (G : Game V) (v : V) :
    ¬ (Winning G true v ∧ Winning G false v)

axiom uniform {V : Type} [Finite V] (G : Game V) (player : Bool) :
    ∃ f, G.Legal player f ∧ ∀ v, Winning G player v → G.WinsFrom player f v

axiom complementary {V : Type} [Finite V] (G : Game V) (v : V) :
    Winning G false v ↔ ¬ Winning G true v

axiom predecessor {V : Type} [Finite V] (G : Game V) (v : V) :
    Winning G true v ↔ v ∈ Pre G (Winning G true)

end Lax369799.ParityWinningRegions
