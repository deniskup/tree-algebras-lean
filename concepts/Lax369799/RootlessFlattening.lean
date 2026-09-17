import Lax369799.RootExpansion
import Lax369799.Flattening

/-!
---
title: Reachable substitution with root-free components
type: theorem
---
When every component has no roots, pruning unreachable outer vertices
before substitution is sound. One may first restrict each component and
then the outer pattern to reachable vertices. The resulting reachable
flattening covers the reachable restriction of the original substitution.
-/
namespace Lax369799.RootlessFlattening
open RankedSystems

noncomputable def trimLabels {A : RankedSet} {n : ℕ} {V : Type}
    (P : Presentation (FinitePresentations.FiniteSystem A) n V) :
    Presentation (SetSystem A) n V := {
  P with label := fun v => ⟨(P.label v).1, trim (FinitePresentations.Inner P v).graph⟩ }

axiom flatten_cover {A : RankedSet} {n : ℕ} {V : Type} [Fintype V]
    (P : Presentation (FinitePresentations.FiniteSystem A) n V)
    (h : ∀ v, (FinitePresentations.Inner P v).graph.root = ∅) :
    Morphisms.UnfoldsTo (trim (FinitePresentations.flattenPresentation P))
      (Flattening.flatten (trim (trimLabels P)))

end Lax369799.RootlessFlattening
