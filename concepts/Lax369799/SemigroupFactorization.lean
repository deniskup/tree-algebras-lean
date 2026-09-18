import Lax369799.WordFactorization
import Mathlib.Algebra.Group.WithOne.Basic
import Mathlib.Data.Fintype.Option

/-!
---
title: Stable factorization with recurrent vertices
type: theorem
---
A word over a finite semigroup admits stable idempotent blocks without
assuming an identity element. For a simultaneous sequence in a finite
vertex set, all block boundaries can be chosen at the same vertex. This
is the factorization used to turn a branch into a periodic branch in
Section 6.3.
-/
namespace Lax369799.SemigroupFactorization

/-- Product of a nonempty interval [i,j), starting with its first letter. -/
def block {M : Type} [Semigroup M] (w : ℕ → M) (i j : ℕ) : M :=
  ((List.range' (i + 1) (j - i - 1)).map w).foldl (· * ·) (w i)

axiom factorization {M V : Type} [Semigroup M] [Finite M] [Finite V]
    (w : ℕ → M) (v : ℕ → V) :
    ∃ (cut : ℕ → ℕ) (a e : M) (r : V), StrictMono cut ∧ 0 < cut 0 ∧
      e * e = e ∧ a * e = a ∧ (∀ i, v (cut i) = r) ∧
      (∀ i, block w 0 (cut i) = a) ∧
      (∀ i j, i < j → block w (cut i) (cut j) = e)

end Lax369799.SemigroupFactorization
