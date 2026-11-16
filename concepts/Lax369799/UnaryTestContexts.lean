import Lax369799.ClosedUnaryLift
import Lax369799.SplitExtremal

/-!
---
title: Normal data for a unary type with a closed continuation
type: theorem
---
After removing a unary hole, a closed continuation is an isolated nullary
component of each unary piece. It is initial only in the outgoing piece.
The incoming testing prefix is planted in both pieces. These data turn a
binary sum of continuations into the meet of the two normal data.
-/
namespace Lax369799.UnaryTestContexts
open RankedSystems (RankedSet)
open FinitePresentations FiniteSyntacticAlgebra FiniteContextualOrder FiniteAcceptance
open ExtremalContexts (Data)

noncomputable def data {A : RankedSet} (E : Algebra A) (root : Prop) (t : A 1) (c : A 0) : Data A 1 :=
  (⟨root, ∅⟩, fun i => sumValue E (E.eval 1 (plant (atomic t)))
    (ClosedUnaryLift.value E (i == 1) c))

axiom data_sum {A : RankedSet} (L : Algebras.Language A)
    (E : Algebra (Carrier (Accepting L)))
    (hE : ∀ n (S : FiniteSystem (FiniteSystem A) n),
      E.eval n (relabel (quotientMap (Accepting L)) S) = quotientMap (Accepting L) n (flatten S))
    (root : Prop) (t : Carrier (Accepting L) 1) (c d : Carrier (Accepting L) 0) :
    data E root t (sumValue E c d) = SplitExtremal.meetData E (data E root t c) (data E root t d)

end Lax369799.UnaryTestContexts
