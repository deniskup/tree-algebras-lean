import Lax369799.FiniteBranchWords

/-!
---
title: Unary types preserving explicit choices
type: theorem
---
Selected unary types must preserve the binary choice operation on closed
continuations. This is a necessary restriction for exposing choices as
separate branch tests. It is not asserted of all unary algebra elements.
Finite words of such types preserve choices, and finite expressions built
from them can be tested path by path. Existence of suitable selected types
and extension to cyclic presentations are separate obligations.
-/
namespace Lax369799.ChoicePreservingUnary
open RankedSystems (RankedSet)
open FiniteSyntacticAlgebra FiniteBranchWords

def PreservesChoices {A : RankedSet} (E : Algebra A) (b : A 1) : Prop :=
  ∀ c d : A 0, act E b (sumValue E c d) = sumValue E (act E b c) (act E b d)

/-- The eligible unary types, retaining their proof of choice preservation. -/
def TypeSet {A : RankedSet} (E : Algebra A) := {b : A 1 // PreservesChoices E b}

inductive Expression (A : RankedSet) where
  | leaf : A 0 → Expression A
  | step : A 1 → Expression A → Expression A
  | choice : Expression A → Expression A → Expression A

def Expression.eval {A : RankedSet} (E : Algebra A) : Expression A → A 0
  | .leaf a => a
  | .step b t => act E b (t.eval E)
  | .choice s t => sumValue E (s.eval E) (t.eval E)

def Expression.Eligible {A : RankedSet} (E : Algebra A) : Expression A → Prop
  | .leaf _ => True
  | .step b t => PreservesChoices E b ∧ t.Eligible E
  | .choice s t => s.Eligible E ∧ t.Eligible E

def Expression.paths {A : RankedSet} : Expression A → List (List (A 1) × A 0)
  | .leaf a => [([], a)]
  | .step b t => t.paths.map (fun p => (b :: p.1, p.2))
  | .choice s t => s.paths ++ t.paths

axiom word_preserves_choices {A : RankedSet} (E : Algebra A)
    (w : List (A 1)) (hw : ∀ b ∈ w, PreservesChoices E b) (c d : A 0) :
    value E w (sumValue E c d) = sumValue E (value E w c) (value E w d)

axiom finite_branch_test {A : RankedSet} (E : Algebra A) (F : Set (A 0))
    (hF : ∀ c d, sumValue E c d ∈ F ↔ c ∈ F ∧ d ∈ F)
    (t : Expression A) (ht : t.Eligible E) :
    t.eval E ∈ F ↔ ∀ p ∈ t.paths, value E p.1 p.2 ∈ F

axiom finite_types {A : RankedSet} (E : Algebra A) [Finite (A 1)] : Finite (TypeSet E)

end Lax369799.ChoicePreservingUnary
