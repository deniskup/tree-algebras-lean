import Lax369799.FiniteBranchWords

/-!
---
title: The unary semigroup and its action
type: theorem
---
Unary values compose by evaluating a two-vertex chain. Associativity of
the algebra makes this composition associative, and the same operation
acts on every sort. This supplies the finite semigroup used to factor
infinite unary branch words in Section 6.3.
-/

namespace Lax369799.UnaryComposition
open RankedSystems (RankedSet)
open FinitePresentations FiniteSyntacticAlgebra

def application {A : RankedSet} {n : ℕ} (b : A 1) (a : A n) : FiniteSystem A n where
  size := 2
  graph := {
    label := Fin.cases ⟨1, b⟩ (fun _ => ⟨n, a⟩)
    initial := {0}
    root := ∅
    edge := fun v d t =>
      (v = 0 ∧ d = 0 ∧ t = .inl 1) ∨
      (v = 1 ∧ ∃ j : Fin n, d = j.val ∧ t = .inr j)
    direction_valid := by
      rintro v d t (⟨rfl, rfl, _⟩ | ⟨rfl, j, rfl, _⟩)
      · exact Nat.zero_lt_one
      · exact j.isLt }

def act {A : RankedSet} (E : Algebra A) {n : ℕ} (b : A 1) (a : A n) : A n :=
  E.eval n (application b a)

def product {A : RankedSet} (E : Algebra A) (a b : A 1) : A 1 := act E a b

axiom action_law {A : RankedSet} (E : Algebra A) {n : ℕ}
    (a b : A 1) (c : A n) : act E (product E a b) c = act E a (act E b c)

axiom associative {A : RankedSet} (E : Algebra A) (a b c : A 1) :
    product E (product E a b) c = product E a (product E b c)

axiom nullary_action {A : RankedSet} (E : Algebra A) (b : A 1) (a : A 0) :
    act E b a = FiniteBranchWords.act E b a

end Lax369799.UnaryComposition
