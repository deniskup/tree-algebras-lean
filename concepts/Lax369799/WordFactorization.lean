import Lax369799.InfiniteRamsey
import Mathlib.Algebra.BigOperators.Group.List.Basic

/-!
---
title: Idempotent factorization of infinite words
type: theorem
---
An infinite word in a finite monoid has a nonempty initial block of value
`a`, followed by nonempty blocks of a common idempotent value `e`, with
`a * e = a`. The increasing cuts are cofinal and every union of consecutive
blocks after the first again has value `e`.
-/
namespace Lax369799.WordFactorization

/-- Product of the half-open interval of letters [i,j). -/
def block {M : Type} [Monoid M] (w : ℕ → M) (i j : ℕ) : M :=
  ((List.range' i (j - i)).map w).prod

axiom factorization {M : Type} [Monoid M] [Finite M] (w : ℕ → M) :
    ∃ (cut : ℕ → ℕ) (a e : M), StrictMono cut ∧ 0 < cut 0 ∧
      e * e = e ∧ a * e = a ∧
      (∀ i, block w 0 (cut i) = a) ∧
      (∀ i j, i < j → block w (cut i) (cut j) = e)

end Lax369799.WordFactorization
