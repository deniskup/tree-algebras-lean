import Lax369799.UnfoldAutomata

/-!
---
title: Recurring priorities in finite-state runs
type: theorem
---
A run over finitely many states has a unique least recurring priority.
Finite prefixes do not affect recurrence. A state with this least priority
occurs twice arbitrarily far out, with no lower priority between the two
occurrences; this is the cycle used in periodic branch arguments.
-/
namespace Lax369799.WordParity

def Recurrent (p : ℕ → ℕ) (c : ℕ) : Prop := ∀ N, ∃ n, N ≤ n ∧ p n = c

def LeastRecurring (p : ℕ → ℕ) (c : ℕ) : Prop :=
  Recurrent p c ∧ ∀ b, b < c → ∃ N, ∀ n, N ≤ n → p n ≠ b

axiom least_recurring {Q : Type} [Finite Q] (priority : Q → ℕ) (r : ℕ → Q) :
    ∃! c, LeastRecurring (fun n => priority (r n)) c

axiom recurrent_shift (p : ℕ → ℕ) (c k : ℕ) :
    Recurrent (fun n => p (n + k)) c ↔ Recurrent p c

axiom minimum_cycle {Q : Type} [Finite Q] (priority : Q → ℕ) (r : ℕ → Q)
    (c : ℕ) (hc : LeastRecurring (fun n => priority (r n)) c) (N : ℕ) :
    ∃ i j, N ≤ i ∧ i < j ∧ r i = r j ∧ priority (r i) = c ∧
      ∀ k, i ≤ k → k ≤ j → c ≤ priority (r k)

axiom acceptance_iff {u z : ℕ} (D : UnfoldAutomata.WordCondition u z)
    (w : ℕ → Fin u) (c : ℕ)
    (hc : LeastRecurring (fun n => D.priority (D.run w n)) c) :
    D.AcceptsInfinite w ↔ Even c

end Lax369799.WordParity
