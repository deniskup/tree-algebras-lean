import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Finset.Lattice.Fold

/-!
---
title: Eventual membership in finite families
type: theorem
---
For a sequence of subsets of a finite set, every sufficiently late set
contains only elements occurring infinitely often. One threshold works
for finitely many such sequences. This is the finite stabilization step
for the compressed transitions in Lemma 108.
-/

namespace Lax369799.FiniteRecurrence

def Recurrent {X : Type} (F : ℕ → Set X) : Set X :=
  {x | ∀ N, ∃ k, N ≤ k ∧ x ∈ F k}

axiom eventual_subset {X : Type} [Finite X] (F : ℕ → Set X) :
    ∃ N, ∀ k, N ≤ k → F k ⊆ Recurrent F

axiom simultaneous {I X : Type} [Finite I] [Finite X] (F : I → ℕ → Set X) :
    ∃ N, ∀ i k, N ≤ k → F i k ⊆ Recurrent (F i)

end Lax369799.FiniteRecurrence
