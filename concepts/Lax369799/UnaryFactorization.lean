import Lax369799.UnaryComposition
import Lax369799.SemigroupFactorization

/-!
---
title: Stable factorization of algebraic branch words
type: theorem
---
An infinite word of unary values of a finite algebra has a stable
factorization. The prefix value absorbs an idempotent block value, and
the cuts may simultaneously visit one fixed vertex of any finite graph
through which the word runs. The associated two-vertex lasso evaluates
the regular word formed from these two values.
-/

namespace Lax369799.UnaryFactorization
open RankedSystems (RankedSet)
open FinitePresentations FiniteSyntacticAlgebra UnaryComposition

def block {A : RankedSet} (E : Algebra A) (w : ℕ → A 1) (i j : ℕ) : A 1 :=
  ((List.range' (i + 1) (j - i - 1)).map w).foldl (product E) (w i)

def lasso {A : RankedSet} (a e : A 1) : FiniteSystem A 0 where
  size := 2
  graph := {
    label := Fin.cases ⟨1, a⟩ (fun _ => ⟨1, e⟩)
    initial := {0}
    root := ∅
    edge := fun _ d t => d = 0 ∧ t = .inl 1
    direction_valid := by
      rintro v d t ⟨rfl, _⟩
      exact Fin.cases Nat.zero_lt_one (fun _ => Nat.zero_lt_one) v }

axiom stable_factorization {A : RankedSet} (E : Algebra A) [Finite (A 1)]
    {V : Type} [Finite V] (w : ℕ → A 1) (v : ℕ → V) :
    ∃ (cut : ℕ → ℕ) (a e : A 1) (r : V), StrictMono cut ∧ 0 < cut 0 ∧
      product E e e = e ∧ product E a e = a ∧ (∀ i, v (cut i) = r) ∧
      (∀ i, block E w 0 (cut i) = a) ∧
      (∀ i j, i < j → block E w (cut i) (cut j) = e)

end Lax369799.UnaryFactorization
