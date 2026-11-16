import Lax369799.ExpandedSyntacticAlgebra

/-!
---
title: Unions of initial and root marks
type: theorem
---
For three presentations with the same labels and edges, union of their
initial and root marks evaluates to the meet of the two separate values.
The covering map folds the two copies of each vertex together.
-/
namespace Lax369799.FiniteMarkUnion
open RankedSystems (RankedSet Presentation)
open FinitePresentations FiniteSyntacticAlgebra FiniteContextualOrder FiniteAcceptance

axiom evaluation_union {A : RankedSet} (L : Algebras.Language A)
    (E : ExpandedSyntacticAlgebra.SyntacticAlgebra L) {n : ℕ} {V : Type} [Fintype V]
    (G H K : Presentation (Carrier (Accepting L)) n V)
    (hl : ∀ v, G.label v = K.label v ∧ H.label v = K.label v)
    (hi : ∀ v, K.initial v ↔ G.initial v ∨ H.initial v)
    (hr : ∀ v, K.root v ↔ G.root v ∨ H.root v)
    (he : ∀ v d t, (G.edge v d t ↔ K.edge v d t) ∧ (H.edge v d t ↔ K.edge v d t)) :
    E.algebra.eval n (enumerate K) = sumValue E.algebra
      (E.algebra.eval n (enumerate G)) (E.algebra.eval n (enumerate H))

end Lax369799.FiniteMarkUnion
