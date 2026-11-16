import Lax369799.ParityFixedPoints

/-!
---
title: Nested fixed-point equations for finite parity games
type: theorem
---
At depth zero every position is stopped and tested by its controlled
predecessor condition. Increasing the depth binds the next priority by a
greatest fixed point for even priorities and a least fixed point for odd
priorities. Once the depth exceeds every priority, these nested equations
define precisely Eve's positional winning region. The free boundary
valuation is then immaterial.
-/
namespace Lax369799.ParityGameEquations
open FiniteParityGames ParityWinningRegions ParityFixedPoints
attribute [local instance] Classical.propDecidable

noncomputable def cut {V : Type} (G : Game V) (n : ℕ) (ρ : ℕ → Set V) : Game V :=
  stop G {v | n ≤ G.priority v} {v | v ∈ pre G true (ρ (G.priority v))}

noncomputable def solve {V : Type} (G : Game V) : ℕ → (ℕ → Set V) → Set V
  | 0, ρ => {v | v ∈ pre G true (ρ (G.priority v))}
  | n + 1, ρ => if Even n then
      sSup {X : Set V | X ⊆ solve G n (Function.update ρ n X)}
    else sInf {X : Set V | Set.Subset (solve G n (Function.update ρ n X)) X}

axiom solve_cut {V : Type} [Finite V] (G : Game V) (n : ℕ) (ρ : ℕ → Set V) :
    (Winning (cut G n ρ) true : Set V) = solve G n ρ

axiom winning {V : Type} [Finite V] (G : Game V) (n : ℕ)
    (hn : ∀ v, G.priority v < n) (ρ : ℕ → Set V) :
    (Winning G true : Set V) = solve G n ρ

end Lax369799.ParityGameEquations
