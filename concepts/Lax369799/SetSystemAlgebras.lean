import Lax369799.ExpandedSyntacticAlgebra

/-!
---
title: Set-algebras with retained vertices
type: theorem
---
Definition 63 evaluates all finite set-systems, including unreachable
vertices. Its axioms are the atomic unit, associativity, invariance under
unfold-equivalence, and the reverse comparison for morphisms. There is
no continuity axiom. Foldings here are locally surjective covers that are
also surjective on all vertices, as in Definitions 8 and 18.
The yield-syntactic quotient has this structure, with its contextual
order equal to the order induced by binary disjoint union.
-/

namespace Lax369799.SetSystemAlgebras
open RankedSystems (RankedSet)
open FinitePresentations FiniteSyntacticAlgebra

def UnfoldEquivalent {A : RankedSet} {n : ℕ} (S T : FiniteSystem A n) : Prop :=
  ∃ U : FiniteSystem A n,
    ∃ f : PresentationCovers.Cover U.graph S.graph,
    ∃ g : PresentationCovers.Cover U.graph T.graph,
      Function.Surjective f.toFun ∧ Function.Surjective g.toFun

structure SetAlgebra (A : RankedSet) extends Algebra A where
  unfold_invariant : ∀ n (S T : FiniteSystem A n),
    UnfoldEquivalent S T → eval n S = eval n T
  morphism : ∀ n (S T : FiniteSystem A n), Nonempty (FiniteMorphisms.Morphism S T) →
    sumValue toAlgebra (eval n T) (eval n S) = eval n T

def Below {A : RankedSet} (E : SetAlgebra A) {n : ℕ} (a b : A n) : Prop :=
  sumValue E.toAlgebra a b = a

structure Morphism {A B : RankedSet} (E : SetAlgebra A) (D : SetAlgebra B) where
  map : RankedSystems.RankedMap A B
  commutes : ∀ n (S : FiniteSystem A n),
    D.eval n (relabel map S) = map n (E.eval n S)

axiom folding_invariance {A : RankedSet} (E : SetAlgebra A) {n : ℕ}
    (S T : FiniteSystem A n) (f : PresentationCovers.Cover S.graph T.graph)
    (hf : Function.Surjective f.toFun) : E.eval n S = E.eval n T

axiom eval_sum {A : RankedSet} (E : SetAlgebra A) {n : ℕ} (S T : FiniteSystem A n) :
    E.eval n (sum S T) = sumValue E.toAlgebra (E.eval n S) (E.eval n T)

axiom meet_laws {A : RankedSet} (E : SetAlgebra A) (n : ℕ) :
    (∀ a b c : A n, sumValue E.toAlgebra (sumValue E.toAlgebra a b) c =
      sumValue E.toAlgebra a (sumValue E.toAlgebra b c)) ∧
    (∀ a b : A n, sumValue E.toAlgebra a b = sumValue E.toAlgebra b a) ∧
    (∀ a : A n, sumValue E.toAlgebra a a = a)

axiom order_laws {A : RankedSet} (E : SetAlgebra A) (n : ℕ) :
    (∀ a : A n, Below E a a) ∧
    (∀ a b : A n, Below E a b → Below E b a → a = b) ∧
    (∀ a b c : A n, Below E a b → Below E b c → Below E a c) ∧
    (∀ a b c : A n, Below E c (sumValue E.toAlgebra a b) ↔ Below E c a ∧ Below E c b)

axiom evaluation_monotone {A B : RankedSet} (E : SetAlgebra A) {n : ℕ}
    (P : FiniteSystem B n) (q r : ∀ v : P.Vertex, A (P.graph.label v).1)
    (h : ∀ v, Below E (q v) (r v)) :
    Below E (E.eval n (withLabels P q)) (E.eval n (withLabels P r))

axiom syntactic_order {A : RankedSet} (L : Algebras.Language A)
    (E : ExpandedSyntacticAlgebra.SyntacticAlgebra L) {n : ℕ}
    (a b : FiniteContextualOrder.Carrier (FiniteAcceptance.Accepting L) n) :
    FiniteContextualOrder.ClassBelow (FiniteAcceptance.Accepting L) a b ↔
      sumValue E.algebra a b = a

axiom syntactic_structure {A : RankedSet} (L : Algebras.Language A)
    (E : ExpandedSyntacticAlgebra.SyntacticAlgebra L) :
    ∃ D : SetAlgebra (FiniteContextualOrder.Carrier (FiniteAcceptance.Accepting L)),
      D.toAlgebra = E.algebra

end Lax369799.SetSystemAlgebras
