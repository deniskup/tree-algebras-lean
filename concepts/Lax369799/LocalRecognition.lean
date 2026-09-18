import Lax369799.PathAlgebra

/-!
---
title: Recognition of local vertex and edge tests
type: theorem
---
Finite path-summary algebras recognize the presence of a vertex satisfying
a letter predicate, and the presence of an edge whose endpoints satisfy
two specified letter predicates. Reachability from the unique initial
vertex makes these global existence tests into path tests.
-/
namespace Lax369799.LocalRecognition
open RankedSystems Algebras

axiom occurrence {A : RankedSet} (p : ∀ n, A n → Prop) :
  Recognizable {S : System A 0 | ∃ v, p _ (S.val.graph.label v).2}

axiom edge {A : RankedSet} (p q : ∀ n, A n → Prop) :
  Recognizable {S : System A 0 | ∃ v w d,
    p _ (S.val.graph.label v).2 ∧ q _ (S.val.graph.label w).2 ∧ S.val.graph.edge v d (.inl w)}

end Lax369799.LocalRecognition
