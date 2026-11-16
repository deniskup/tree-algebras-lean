import Lax369799.QuantitativeRecognition
import Lax369799.FiniteContextualOrder
import Lax369799.FiniteAcceptance
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
---
title: Computable bounds on the syntactic nullary and unary sorts
type: theorem
---
The number of possible small profile entries is bounded by a finite sum.
Initial and root profile codes give a bound on each contextual quotient
without computing equivalence of contexts. This is the quantitative
step used in the effectivity argument after Theorem 2.
-/

namespace Lax369799.QuantitativeProfiles

def entryBound (f : ℕ → ℕ) (bound n : ℕ) : ℕ :=
  ∑ k ∈ Finset.range (n*bound+1),f k*n^k

def quotientBound (f : ℕ → ℕ) (n : ℕ) : ℕ :=
  2 ^ (2*entryBound f (f 1+1) n)

open RankedSystems Algebras QuantitativeRecognition

axiom syntactic_bound {A : RankedSet} (L : Language A) (hL : UnfoldInvariantLanguage L)
    (f : ℕ → ℕ) (hrec : Bound f L) (n : ℕ) :
    Nat.card (FiniteContextualOrder.Carrier (FiniteAcceptance.Accepting L) n) ≤ quotientBound f n

end Lax369799.QuantitativeProfiles