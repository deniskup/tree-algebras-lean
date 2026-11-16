import Lax369799.FiniteSyntacticAlgebra

/-!
---
title: Closed values as unary pieces
type: theorem
---
A nullary value can occur in a unary piece with an unused output variable.
Its vertex can be initial or unmarked. Both operations preserve binary
sums; unmarked vertices are retained during substitution.
-/
namespace Lax369799.ClosedUnaryLift
open RankedSystems (RankedSet)
open FinitePresentations FiniteSyntacticAlgebra

def system {A : RankedSet} (initial : Bool) (c : A 0) : FiniteSystem A 1 where
  size := 1
  graph := {
    label := fun _ => ⟨0, c⟩
    initial := fun _ => initial = true
    root := ∅
    edge := fun _ _ _ => False
    direction_valid := fun _ _ _ h => False.elim h }

def value {A : RankedSet} (E : Algebra A) (initial : Bool) (c : A 0) : A 1 :=
  E.eval 1 (system initial c)

axiom preserves_sum {A : RankedSet} (E : Algebra A) (initial : Bool) (c d : A 0) :
    value E initial (sumValue E c d) = sumValue E (value E initial c) (value E initial d)

end Lax369799.ClosedUnaryLift
