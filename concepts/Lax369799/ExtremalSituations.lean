import Lax369799.ExpandedSyntacticAlgebra
import Lax369799.ExtremalUnaryTypes
import Lax369799.FiniteLocalReplacement

/-!
---
title: Extremal accepted situations in the syntactic algebra
type: theorem
---
Sections 5.1–5.2 minimize the element in the hole as well as its context
pieces. In the syntactic algebra, planting allows context pieces to be
recorded by their unary values, a root flag, and self-loop directions.
An extremal situation is a componentwise minimal accepted pair of these
data and an element. This is the planted form of Definition 85.
Unlike extremality of context data for a fixed element, it also forces
every accepted decrease of that element to be equal to it.
-/

namespace Lax369799.ExtremalSituations
open RankedSystems (RankedSet)
open FinitePresentations FiniteContexts FiniteContextualOrder FiniteSyntacticAlgebra
open FiniteAcceptance ExpandedSyntacticAlgebra
open ExtremalContexts (Data)

abbrev Situation {A : RankedSet} (F : ClosedProperty A) (k : ℕ) :=
  Data (Carrier F) k × Carrier F k

def Below {A : RankedSet} (F : ClosedProperty A) {k : ℕ}
    (x y : Situation F k) : Prop :=
  FiniteExtremal.DataBelow F x.1 y.1 ∧ ClassBelow F x.2 y.2

def Accepted {A : RankedSet} (F : ClosedProperty A) (E : Algebra (Carrier F))
    {k : ℕ} (x : Situation F k) : Prop :=
  FiniteExtremal.Accepts F E x.2 x.1

def IsExtremal {A : RankedSet} (F : ClosedProperty A) (E : Algebra (Carrier F))
    {k : ℕ} (x : Situation F k) : Prop :=
  Accepted F E x ∧ ∀ y, Below F y x → Accepted F E y → y = x

def ExtremalElement {A : RankedSet} (F : ClosedProperty A) (E : Algebra (Carrier F))
    {k : ℕ} (a : Carrier F k) : Prop :=
  ∃ x : Data (Carrier F) k, IsExtremal F E (x, a)

axiom choice {A : RankedSet} (F : ClosedProperty A) (E : Algebra (Carrier F))
    (hfinite : ∀ n, Finite (Carrier F n)) {k : ℕ} (x : Situation F k)
    (hx : Accepted F E x) :
    ∃ y, Below F y x ∧ IsExtremal F E y

axiom replacement {A : RankedSet} (L : Algebras.Language A)
    (hL : Algebras.UnfoldInvariantLanguage L) (hrec : Algebras.Recognizable L)
    (E : SyntacticAlgebra L) {k : ℕ}
    (C : Context (Carrier (Accepting L)) k 0) (a : Carrier (Accepting L) k)
    (ha : AcceptingClass (Accepting L) (E.algebra.eval 0 (plug C (atomic a)))) :
    ∃ b, ExtremalElement (Accepting L) E.algebra b ∧ ClassBelow (Accepting L) b a ∧
      AcceptingClass (Accepting L) (E.algebra.eval 0 (plug C (atomic b)))

axiom simultaneous {A B : RankedSet} (L : Algebras.Language A)
    (hL : Algebras.UnfoldInvariantLanguage L) (hrec : Algebras.Recognizable L)
    (E : SyntacticAlgebra L) (P : FiniteSystem B 0)
    (q : ∀ v : P.Vertex, Carrier (Accepting L) (P.graph.label v).1) :
    AcceptingClass (Accepting L) (E.algebra.eval 0 (withLabels P q)) ↔
      ∃ r : ∀ v : P.Vertex, Carrier (Accepting L) (P.graph.label v).1,
        (∀ v, ExtremalElement (Accepting L) E.algebra (r v) ∧
          ClassBelow (Accepting L) (r v) (q v)) ∧
        AcceptingClass (Accepting L) (E.algebra.eval 0 (withLabels P r))

axiom fixed_element {A : RankedSet} (F : ClosedProperty A) (E : Algebra (Carrier F))
    {k : ℕ} (x : Data (Carrier F) k) (a : Carrier F k)
    (hx : IsExtremal F E (x, a)) : FiniteExtremal.IsExtremal F E a x

axiom split_value {A : RankedSet} (L : Algebras.Language A)
    (E : SyntacticAlgebra L) {k : ℕ} (hk : 1 ≤ k)
    (x : Data (Carrier (Accepting L)) k) (a : Carrier (Accepting L) k)
    (hx : IsExtremal (Accepting L) E.algebra (x, a)) :
    E.algebra.eval k (SplitExtremal.delta x.1 x.2 a) = a

axiom normal_test {A : RankedSet} (L : Algebras.Language A)
    (E : SyntacticAlgebra L) {k : ℕ}
    (x : Data (Carrier (Accepting L)) k) (a : Carrier (Accepting L) k)
    (hx : IsExtremal (Accepting L) E.algebra (x, a))
    (y : Data (Carrier (Accepting L)) k) :
    FiniteExtremal.Accepts (Accepting L) E.algebra a y ↔
      FiniteExtremal.DataBelow (Accepting L) x y

axiom unary_selected {A : RankedSet} (L : Algebras.Language A)
    (E : SyntacticAlgebra L) (b : Carrier (Accepting L) 1)
    (hb : ExtremalElement (Accepting L) E.algebra b) :
    ExtremalUnaryTypes.Selected L E b

axiom parallel_decomposition {A : RankedSet} (L : Algebras.Language A)
    (E : SyntacticAlgebra L) {k : ℕ} (hk : 1 ≤ k) (a : Carrier (Accepting L) k)
    (ha : ExtremalElement (Accepting L) E.algebra a) :
    ∃ b : Fin k → Carrier (Accepting L) 1,
      E.algebra.eval k (ofSetSystem (DeterministicElements.parallel b)) = a

end Lax369799.ExtremalSituations
