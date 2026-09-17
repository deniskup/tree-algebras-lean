import Lax369799.AutomatonProperty

/-!
---
title: The automaton property of syntactic set-algebras
type: theorem
---
A rankwise-finite set-algebra with a plant-invariant accepting principal
filter that separates the order has the automaton property
(`lemma:ya-automaton-property`). The accepting filter of the syntactic
set-algebra of a rankwise-finite recognisable regular-tree language has
this property (`cor:synt-aut-prop`).
-/

namespace Lax369799.AutomatonPropertyTheorem
open RankedSystems Algebras SetAlgebras SyntacticOrder AutomatonProperty

axiom automaton_property {A : RankedSet} (E : SetAlgebra A)
    (hA : RankwiseFinite A) (f : A 0)
    (hp : PlantInvariant E f) (hs : OrderSeparating E f) : HasAutomatonProperty E f

axiom syntactic_automaton_property {A : RankedSet} (L : Language A)
    (hL : UnfoldInvariantLanguage L) (hA : Recognizable L) :
    ∃ (E : SyntacticAlgebra L) (f : SyntacticCarrier L 0),
      HasAutomatonProperty E.algebra f ∧
      ∀ S, Below E.algebra f (syntacticMap L 0 S) ↔ Accepting L S

end Lax369799.AutomatonPropertyTheorem
