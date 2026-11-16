import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.Group.Nat.Even

/-!
---
title: Positional determinacy of finite parity games
type: theorem
---
A finite parity game admits positional winning strategies for both
players on their winning regions. The arena is total. In this interface
the greatest priority occurring infinitely often is even for Eve to win;
reversing a bounded priority function converts this to the least-priority
convention.
-/

namespace Lax369799.FiniteParityGames

structure Game (V : Type) where
  eve : V → Prop
  edge : V → V → Prop
  priority : V → ℕ
  total : ∀ v, ∃ w, edge v w

def Game.IsPlay {V : Type} (G : Game V) (p : ℕ → V) : Prop :=
  ∀ n, G.edge (p n) (p (n + 1))

def Game.EveWins {V : Type} (G : Game V) (p : ℕ → V) : Prop :=
  ∃ c, ((∀ N, ∃ n, N ≤ n ∧ G.priority (p n) = c) ∧
    (∀ b, c < b → ¬ ∀ N, ∃ n, N ≤ n ∧ G.priority (p n) = b)) ∧ Even c

def Game.Legal {V : Type} (G : Game V) (eve : Bool) (f : V → V) : Prop :=
  ∀ v, (G.eve v ↔ eve = true) → G.edge v (f v)

def Game.Consistent {V : Type} (G : Game V) (eve : Bool)
    (f : V → V) (p : ℕ → V) : Prop :=
  ∀ n, (G.eve (p n) ↔ eve = true) → p (n + 1) = f (p n)

def Game.WinsFrom {V : Type} (G : Game V) (eve : Bool) (f : V → V) (v : V) : Prop :=
  ∀ p, G.IsPlay p → p 0 = v → G.Consistent eve f p → (G.EveWins p ↔ eve = true)

axiom positional_determinacy {V : Type} [Finite V] (G : Game V) :
    ∃ f g : V → V, G.Legal true f ∧ G.Legal false g ∧
      ∀ v, G.WinsFrom true f v ∨ G.WinsFrom false g v

end Lax369799.FiniteParityGames
