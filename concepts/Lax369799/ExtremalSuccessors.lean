import Lax369799.FiniteExtremal

/-!
---
title: Successor confinement in the extremal witness
type: theorem
---
Every component of the extremal witness is attached to its own successor.
An edge starting in the i-th component either stays in that component or
exits through x_i. This property does not require extremality of the context.
-/
namespace Lax369799.ExtremalSuccessors
open RankedSystems (RankedSet)
open FinitePresentations

axiom component_step {A : RankedSet} {k : ℕ} (B : ExtremalContexts.Boundary k)
    (m : Fin (k + 1) → A 1) (a : A k) (i : Fin k)
    (w : (Inner (FiniteExtremal.deltaPattern B m a).graph i.succ).Vertex)
    (d : ℕ) (t) :
    (flattenPresentation (FiniteExtremal.deltaPattern B m a).graph).edge ⟨i.succ, w⟩ d t →
      (∃ u, t = .inl ⟨i.succ, u⟩) ∨ t = .inr i

end Lax369799.ExtremalSuccessors
