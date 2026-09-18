import Mathlib.Order.Monotone.Basic
import Mathlib.Data.Finite.Defs

/-!
---
title: Infinite Ramsey theorem for pairs
type: theorem
---
A coloring of increasing pairs of natural numbers with finitely many
colors has an infinite homogeneous subsequence. This supplies the
factorization argument for infinite branch words in Section 6.3.
-/
namespace Lax369799.InfiniteRamsey

axiom pairs {C : Type} [Finite C] (color : ℕ → ℕ → C) :
    ∃ (f : ℕ → ℕ) (c : C), StrictMono f ∧ ∀ i j, i < j → color (f i) (f j) = c

end Lax369799.InfiniteRamsey
