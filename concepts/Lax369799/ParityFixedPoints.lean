import Lax369799.ParityWinningRegions
import Mathlib.Order.FixedPoints

/-!
---
title: Eliminating one priority by a fixed point
type: theorem
---
Stop a finite parity game on a set of vertices with priority p. A stopped
vertex is winning precisely when the player can force a successor in the
parameter set. Repeated visits to that priority select a greatest fixed
point when p is even and a least fixed point when p is odd. Priorities
above p are allowed only at absorbing vertices; this permits the result
to be iterated with previously stopped priorities.
-/
namespace Lax369799.ParityFixedPoints
open FiniteParityGames ParityWinningRegions
attribute [local instance] Classical.propDecidable

def Owned {V : Type} (G : Game V) (player : Bool) (v : V) : Prop :=
  G.eve v ↔ player = true

def pre {V : Type} (G : Game V) (player : Bool) (X : Set V) : Set V :=
  {v | (Owned G player v → ∃ w, G.edge v w ∧ w ∈ X) ∧
    (¬ Owned G player v → ∀ w, G.edge v w → w ∈ X)}

noncomputable def stop {V : Type} (G : Game V) (C W : Set V) : Game V where
  eve := G.eve
  edge := fun v w => if v ∈ C then w = v else G.edge v w
  priority := fun v => if v ∈ C then if v ∈ W then 0 else 1 else G.priority v
  total := by
    classical
    intro v
    by_cases h : v ∈ C
    · exact ⟨v, by simp [h]⟩
    · obtain ⟨w, hw⟩ := G.total v
      exact ⟨w, by simp [h, hw]⟩

noncomputable def phase {V : Type} (G : Game V) (C : Set V) (player : Bool)
    (X : Set V) : Game V :=
  stop G C {v | v ∈ pre G player X ↔ player = true}

axiom greatest {V : Type} [Finite V] (G : Game V) (C : Set V) (p : ℕ)
    (hC : ∀ v ∈ C, G.priority v = p)
    (hbound : ∀ v, p < G.priority v → ∀ w, G.edge v w → w = v)
    (hp : Even p) : (Winning G true : Set V) = (sSup {X : Set V | X ⊆ Winning (phase G C true X) true} : Set V)

axiom least {V : Type} [Finite V] (G : Game V) (C : Set V) (p : ℕ)
    (hC : ∀ v ∈ C, G.priority v = p)
    (hbound : ∀ v, p < G.priority v → ∀ w, G.edge v w → w = v)
    (hp : ¬ Even p) : (Winning G true : Set V) = (sInf {X : Set V | Set.Subset (Winning (phase G C true X) true) X} : Set V)

end Lax369799.ParityFixedPoints
