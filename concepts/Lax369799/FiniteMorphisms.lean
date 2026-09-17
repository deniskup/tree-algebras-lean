import Lax369799.FiniteAcceptance
import Lax369799.PresentationCovers

/-!
---
title: Morphisms of unpruned finite presentations
type: theorem
---
Morphisms preserve labels, marks, and transitions, including at unreachable
vertices. They lift through substitution in a fixed context. Since they
preserve yields on reachable restrictions, they reverse acceptance and
the contextual preorder defined by yield acceptance.
-/

namespace Lax369799.FiniteMorphisms
open RankedSystems (RankedSet)
open FinitePresentations FiniteContexts FiniteContextualOrder FiniteAcceptance

structure Morphism {A : RankedSet} {n : ℕ} (S T : FiniteSystem A n) where
  toFun : S.Vertex → T.Vertex
  initial : ∀ v, S.graph.initial v → T.graph.initial (toFun v)
  root : ∀ v, S.graph.root v → T.graph.root (toFun v)
  label : ∀ v, T.graph.label (toFun v) = S.graph.label v
  edge : ∀ v d t, S.graph.edge v d t → T.graph.edge (toFun v) d (Sum.map toFun id t)

axiom accepting_morphism {A : RankedSet} (L : Algebras.Language A)
    {S T : FiniteSystem A 0} (f : Morphism S T) : Accepting L T → Accepting L S

axiom contextual_morphism {A : RankedSet} (L : Algebras.Language A) {n : ℕ}
    {S T : FiniteSystem A n} (f : Morphism S T) : Below (Accepting L) T S

axiom sum_lower {A : RankedSet} (L : Algebras.Language A) {n : ℕ}
    (S T : FiniteSystem A n) :
    Below (Accepting L) (sum S T) S ∧ Below (Accepting L) (sum S T) T

axiom contextual_cover {A : RankedSet} (L : Algebras.Language A) {n : ℕ}
    {S T : FiniteSystem A n} (f : PresentationCovers.Cover S.graph T.graph) :
    Equivalent (Accepting L) S T

axiom sum_idempotent {A : RankedSet} (L : Algebras.Language A) {n : ℕ}
    (S : FiniteSystem A n) : Equivalent (Accepting L) (sum S S) S

axiom sum_meet {A : RankedSet} (L : Algebras.Language A) {n : ℕ}
    (R S T : FiniteSystem A n) :
    Below (Accepting L) R (sum S T) ↔
      Below (Accepting L) R S ∧ Below (Accepting L) R T

end Lax369799.FiniteMorphisms
