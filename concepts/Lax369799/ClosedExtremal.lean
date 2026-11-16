import Lax369799.ExtremalSituations

/-!
---
title: The closed extremal witness
type: theorem
---
The rank-zero case of Lemma 91 retains the hole and its incoming unary
piece, makes the hole initial, and retains the former initial vertices
as roots. No direction copy or output edge is needed. Testing this closed
witness forces every component of an accepting context above the original
extremal datum. Minimality then identifies its value with the hole value.
-/

namespace Lax369799.ClosedExtremal
open RankedSystems (RankedSet)
open FinitePresentations FiniteContextualOrder FiniteSyntacticAlgebra
open FiniteAcceptance ExpandedSyntacticAlgebra
open ExtremalContexts (Data)
open FiniteExtremal (Accepts value DataBelow)

def witness {A : RankedSet} (x : Data A 0) (a : A 0) : FiniteSystem A 0 where
  size := 2
  graph := {
    label := Fin.cases ⟨0, a⟩ (fun i => ⟨1, x.2 i⟩)
    initial := {0}
    root := fun v => v = 1 ∨ (v = 0 ∧ x.1.root)
    edge := fun v d t => v = 1 ∧ d = 0 ∧ t = .inl 0
    direction_valid := by
      rintro v d t ⟨rfl, rfl, _⟩
      exact Nat.zero_lt_one }

axiom comparison {A : RankedSet} (L : Algebras.Language A)
    (E : SyntacticAlgebra L) (x y : Data (Carrier (Accepting L)) 0)
    (a : Carrier (Accepting L) 0)
    (hx : Lax369799.FiniteExtremal.IsExtremal (Accepting L) E.algebra a x)
    (hy : Accepts (Accepting L) E.algebra (E.algebra.eval 0 (witness x a)) y) :
    DataBelow (Accepting L) x y

axiom in_context {A : RankedSet} (L : Algebras.Language A)
    (E : SyntacticAlgebra L) (x : Data (Carrier (Accepting L)) 0)
    (a : Carrier (Accepting L) 0) :
    ClassBelow (Accepting L) (value E.algebra a x)
      (value E.algebra (E.algebra.eval 0 (witness x a)) x)

axiom below {A : RankedSet} (L : Algebras.Language A)
    (E : SyntacticAlgebra L) (x : Data (Carrier (Accepting L)) 0)
    (a : Carrier (Accepting L) 0)
    (hx : Lax369799.FiniteExtremal.IsExtremal (Accepting L) E.algebra a x) :
    ClassBelow (Accepting L) (E.algebra.eval 0 (witness x a)) a

axiom witness_value {A : RankedSet} (L : Algebras.Language A)
    (E : SyntacticAlgebra L) (x : Data (Carrier (Accepting L)) 0)
    (a : Carrier (Accepting L) 0)
    (hx : Lax369799.ExtremalSituations.IsExtremal (Accepting L) E.algebra (x, a)) :
    E.algebra.eval 0 (witness x a) = a

axiom normal_test {A : RankedSet} (L : Algebras.Language A)
    (E : SyntacticAlgebra L) (x : Data (Carrier (Accepting L)) 0)
    (a : Carrier (Accepting L) 0)
    (hx : Lax369799.ExtremalSituations.IsExtremal (Accepting L) E.algebra (x, a))
    (y : Data (Carrier (Accepting L)) 0) :
    Accepts (Accepting L) E.algebra a y ↔ DataBelow (Accepting L) x y

end Lax369799.ClosedExtremal
