import Lax369799.SetAlgebras

/-!
---
title: Yield-syntactic order and quotient
type: definition
---
A closed set-system is accepting when all its initial and root yields
belong to the language or its planted copy. The yield-syntactic preorder
compares these acceptance tests in every closed context with one hole.
Mutual comparison defines the syntactic equivalence. `SyntacticAlgebra`
records a set-algebra structure on the resulting quotient whose evaluation
commutes with the quotient map. See Section 4.2.
-/

namespace Lax369799.SyntacticOrder
open RankedSystems Morphisms Flattening Algebras SetAlgebras

def Accepting {A : RankedSet} (L : Language A) (S : SetSystem A 0) : Prop :=
  ∀ T, Yield S T → ∃ U : System A 0, U ∈ L ∧ (T = U.val ∨ T = plant U.val)

def SyntacticBelow {A : RankedSet} (L : Language A) {n : ℕ}
    (S T : SetSystem A n) : Prop :=
  ∀ C : SetContext A n 0, Accepting L (plug C S) → Accepting L (plug C T)

def SyntacticEquivalent {A : RankedSet} (L : Language A) {n : ℕ}
    (S T : SetSystem A n) : Prop := SyntacticBelow L S T ∧ SyntacticBelow L T S

abbrev SyntacticCarrier {A : RankedSet} (L : Language A) : RankedSet :=
  fun n => Quot (@SyntacticEquivalent A L n)

def syntacticMap {A : RankedSet} (L : Language A) :
    RankedMap (SetSystem A) (SyntacticCarrier L) := fun _ => Quot.mk _

structure SyntacticAlgebra {A : RankedSet} (L : Language A) where
  algebra : SetAlgebra (SyntacticCarrier L)
  evaluates : ∀ n (S : SetSystem (SetSystem A) n),
    algebra.eval n (relabel (syntacticMap L) S) = syntacticMap L n (flatten S)

end Lax369799.SyntacticOrder
