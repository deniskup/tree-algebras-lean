import Lax369799.OmegaDeterminization

/-!
---
title: Explicit state and priority bounds for word determinization
type: theorem
---
Safra positions admit padded finite-vector encodings. Bounding the full
label-and-mark table and the subsequent appearance record gives numeric
bounds computed from the number of nondeterministic states.
-/

namespace Lax369799.QuantitativeDeterminization

def safraBound (n : ℕ) : ℕ := (2^(n+1))^((n+2)^n)
def stateBound (n : ℕ) : ℕ := safraBound n * (safraBound n)^(safraBound n)
def priorityBound (n : ℕ) : ℕ := 2*safraBound n

open UnfoldAutomata OmegaDeterminization

axiom determinization_bound {u z : ℕ} (B : Buchi u) (bound : ℕ) (hb : B.states ≤ bound) :
    ∃ D : WordCondition u z,
      (∀ w,D.AcceptsInfinite w ↔ B.Accepts w) ∧
      D.states ≤ stateBound bound ∧ (∀ q,D.priority q ≤ priorityBound bound)

end Lax369799.QuantitativeDeterminization