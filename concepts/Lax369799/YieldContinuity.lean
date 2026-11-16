import Lax369799.ContextResolutionApproximation

/-!
---
title: Continuity of yields in a context
type: theorem
---
Corollary 46 of arXiv v6 (Corollary 50 in the revised manuscript), using
the earlier reachable interface: every yield of a substituted context occurs when
the hole is replaced by a finite sum of yields of its label. Conversely,
every such finite sum gives only yields of the original substitution.
The sum stays inside the context, preserving independent choices at
different occurrences. Finite indexed families allow repetitions.
-/
namespace Lax369799.YieldContinuity
open RankedSystems Morphisms Flattening

def sumGraph {A : RankedSet} {n : ℕ} {I : Type} (F : I → SetSystem A n) :
    Presentation A n ((i : I) × (F i).Vertex) where
  label := fun v => (F v.1).graph.label v.2
  initial := fun v => (F v.1).graph.initial v.2
  root := fun v => (F v.1).graph.root v.2
  edge := fun v d t => ∃ s, (F v.1).graph.edge v.2 d s ∧ t = Sum.map (Sigma.mk v.1) id s
  direction_valid := by rintro v d t ⟨s, hs, _⟩; exact (F v.1).graph.direction_valid v.2 d s hs

noncomputable def finiteSum {A : RankedSet} {n : ℕ} {I : Type} [Fintype I]
    (F : I → SetSystem A n) : SetSystem A n := trim (sumGraph F)

axiom continuity {A : RankedSet} {k n : ℕ}
    (C : SetContext A k n) (S : SetSystem A k) (R : SetSystem A n) :
    Yield (plug C S) R ↔
      ∃ (m : ℕ) (F : Fin m → SetSystem A k),
        (∀ i, Yield S (F i)) ∧ Yield (plug C (finiteSum F)) R

end Lax369799.YieldContinuity
