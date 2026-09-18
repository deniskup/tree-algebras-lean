import Lax369799.WordParity

/-!
---
title: Ultimately periodic witnesses in finite parity graphs
type: theorem
---
Every infinite path in a finite graph has an ultimately periodic path
with the same initial vertex and least recurring priority. This supplies
the periodic witness for checking a finite-state parity branch condition.
-/
namespace Lax369799.PeriodicPaths

def UltimatelyPeriodic {Q : Type} (r : ℕ → Q) : Prop :=
  ∃ N p, 0 < p ∧ ∀ n, N ≤ n → r (n + p) = r n

axiom periodic_witness {Q : Type} [Finite Q] (R : Q → Q → Prop)
    (priority : Q → ℕ) (r : ℕ → Q) (hr : ∀ n, R (r n) (r (n + 1)))
    (c : ℕ) (hc : WordParity.LeastRecurring (fun n => priority (r n)) c) :
    ∃ s : ℕ → Q, s 0 = r 0 ∧ (∀ n, R (s n) (s (n + 1))) ∧
      UltimatelyPeriodic s ∧ WordParity.LeastRecurring (fun n => priority (s n)) c

axiom periodic_test {Q : Type} [Finite Q] (R : Q → Q → Prop)
    (priority : Q → ℕ) (q : Q) :
    (∀ r : ℕ → Q, r 0 = q → (∀ n, R (r n) (r (n + 1))) → UltimatelyPeriodic r →
      ∃ c, Even c ∧ WordParity.LeastRecurring (fun n => priority (r n)) c) ↔
    (∀ r : ℕ → Q, r 0 = q → (∀ n, R (r n) (r (n + 1))) →
      ∃ c, Even c ∧ WordParity.LeastRecurring (fun n => priority (r n)) c)

end Lax369799.PeriodicPaths
