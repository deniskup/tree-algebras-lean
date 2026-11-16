import Lax369799.AutomatonProperty

/-!
---
title: The automaton property of syntactic set-algebras
type: theorem
---
A rankwise-finite set-algebra with a plant-invariant accepting principal
filter that separates the order has the automaton property
(`lemma:ya-automaton-property`). The syntactic existence corollary (`cor:synt-aut-prop`) is formulated
with expanded continuity in ExpandedSyntacticAlgebra.
-/

namespace Lax369799.AutomatonPropertyTheorem
open RankedSystems Algebras SetAlgebras SyntacticOrder AutomatonProperty

axiom automaton_property {A : RankedSet} (E : SetAlgebra A)
    (hA : RankwiseFinite A) (f : A 0)
    (hp : PlantInvariant E f) (hs : OrderSeparating E f) : HasAutomatonProperty E f

-- The syntactic existence corollary uses expanded continuity; see
-- ExpandedSyntacticAlgebra.syntactic_automaton_property.

end Lax369799.AutomatonPropertyTheorem
