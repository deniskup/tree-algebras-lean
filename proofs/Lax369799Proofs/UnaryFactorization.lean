import Lax369799.UnaryFactorization
import Lax369799Proofs.UnaryComposition
import Lax369799Proofs.SemigroupFactorization

namespace Lax369799Proofs.UnaryFactorization
open Lax369799.RankedSystems (RankedSet)
open Lax369799.FiniteSyntacticAlgebra Lax369799.UnaryComposition Lax369799.UnaryFactorization

/--
---
conclusion: Lax369799.UnaryFactorization.stable_factorization
---
Equip the unary sort with its checked associative composition. Apply the
finite semigroup factorization while recording the graph vertex at each
cut.
-/
theorem stable_factorization {A : RankedSet} (E : Algebra A) [Finite (A 1)]
    {V : Type} [Finite V] (w : ℕ → A 1) (v : ℕ → V) :
    ∃ (cut : ℕ → ℕ) (a e : A 1) (r : V), StrictMono cut ∧ 0 < cut 0 ∧
      product E e e = e ∧ product E a e = a ∧ (∀ i, v (cut i) = r) ∧
      (∀ i, block E w 0 (cut i) = a) ∧
      (∀ i j, i < j → block E w (cut i) (cut j) = e) := by
  letI : Semigroup (A 1) := { mul := product E, mul_assoc := UnaryComposition.associative E }
  exact SemigroupFactorization.factorization w v

end Lax369799Proofs.UnaryFactorization
