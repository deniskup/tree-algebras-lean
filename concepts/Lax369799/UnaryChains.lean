import Lax369799.UnaryComposition
import Lax369799.UnaryFactorization

/-!
---
title: Evaluation of unary chains in every sort
type: theorem
---
A finite chain of unary letters followed by a value of any rank is
evaluated by successive unary application. For a unary final letter this
computes the semigroup value of a nonempty word.
-/

namespace Lax369799.UnaryChains
open RankedSystems (RankedSet)
open FinitePresentations FiniteSyntacticAlgebra

def path {A : RankedSet} {k n : ℕ} (w : Fin k → A 1) (a : A n) : FiniteSystem A n where
  size := k + 1
  graph := {
    label := Fin.lastCases ⟨n, a⟩ (fun i => ⟨1, w i⟩)
    initial := {0}
    root := ∅
    edge := fun v d t =>
      (∃ i : Fin k, v = i.castSucc ∧ d = 0 ∧ t = .inl i.succ) ∨
      (v = Fin.last k ∧ ∃ j : Fin n, d = j.val ∧ t = .inr j)
    direction_valid := by
      rintro v d t (⟨i, rfl, rfl, rfl⟩ | ⟨rfl, j, rfl, _⟩) <;> simp }

axiom evaluation {A : RankedSet} (E : Algebra A) {k n : ℕ}
    (w : Fin k → A 1) (a : A n) :
    E.eval n (path w a) = (List.ofFn w).foldr (UnaryComposition.act E) a

def word {A : RankedSet} (w : ℕ → A 1) (i k : ℕ) : FiniteSystem A 1 :=
  path (fun t : Fin k => w (i + t.val)) (w (i + k))

axiom word_evaluation {A : RankedSet} (E : Algebra A) (w : ℕ → A 1) (i k : ℕ) :
    E.eval 1 (word w i k) = UnaryFactorization.block E w i (i + k + 1)

end Lax369799.UnaryChains
