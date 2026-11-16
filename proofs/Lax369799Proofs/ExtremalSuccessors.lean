import Lax369799.ExtremalSuccessors

namespace Lax369799Proofs.ExtremalSuccessors
open Lax369799.RankedSystems (RankedSet)
open Lax369799.FinitePresentations

/--
---
conclusion: Lax369799.ExtremalSuccessors.component_step
---
Internal edges keep their component index. An outer edge from component i
has the unique target x_i, so it cannot enter another component.
-/
theorem component_step {A : RankedSet} {k : ℕ} (B : Lax369799.ExtremalContexts.Boundary k)
    (m : Fin (k + 1) → A 1) (a : A k) (i : Fin k)
    (w : (Inner (Lax369799.FiniteExtremal.deltaPattern B m a).graph i.succ).Vertex)
    (d : ℕ) (t) :
    (flattenPresentation (Lax369799.FiniteExtremal.deltaPattern B m a).graph).edge ⟨i.succ, w⟩ d t →
      (∃ u, t = .inl ⟨i.succ, u⟩) ∨ t = .inr i := by
  rintro (⟨u, _, rfl⟩ | ⟨j, _, h⟩)
  · exact Or.inl ⟨u, rfl⟩
  · rcases h with ⟨v, hv, _, rfl⟩ | ⟨l, hl, rfl⟩
    · have hh : Sum.inl v.1 = (Sum.inr i : Fin (k + 1) ⊕ Fin k) := hv.2
      cases hh
    · have hh : (Sum.inr l : Fin (k + 1) ⊕ Fin k) = Sum.inr i := hl.2
      exact Or.inr (congrArg Sum.inr (Sum.inr.inj hh))

end Lax369799Proofs.ExtremalSuccessors
