import Lax369799.AcceptanceObservations
import Lax369799Proofs.PresentationObservations
import Lax369799Proofs.PlantAcceptance

namespace Lax369799Proofs.AcceptanceObservations
open Lax369799.RankedSystems Lax369799.Algebras Lax369799.Morphisms
open Lax369799.PresentationObservations Lax369799.RootExpansion

/--
---
conclusion: Lax369799.AcceptanceObservations.accepting_iff_values
---
Each direct resolution is its own yield. Every yield is unfolding-equivalent
to a direct resolution and therefore has the same observed value. The cover
of the reachable restriction also preserves all root observations.
-/
theorem accepting_iff_values {A B : RankedSet} (E : Algebra B) (hE : UnfoldInvariant E)
    (η : RankedMap A B) (F : Set (B 0)) (L : Language A) (hL : Recognizes E η F L)
    {V : Type} [Fintype V] (G : Presentation A 0 V) :
    Lax369799.SyntacticOrder.Accepting L (trim G) ↔
      values E η G ⊆ F ∧ values E η (startAtRoots G) ⊆ F := by
  rw [← PresentationObservations.root_values_cover E hE η (FiniteAcceptance.trimProjection G)]
  rw [PlantAcceptance.accepting_iff]
  constructor
  · intro h
    constructor
    · rintro b ⟨R, hr, rfl⟩
      exact (hL R).mp (h R (Or.inl ⟨R, hr,
        ⟨MorphismTheorems.identity _, MorphismTheorems.identity_surjective _⟩⟩))
    · rintro b ⟨R, hr, rfl⟩
      exact (hL R).mp (h R (Or.inr ⟨R, hr,
        ⟨MorphismTheorems.identity _, MorphismTheorems.identity_surjective _⟩⟩))
  · rintro ⟨hi, hr⟩ R (⟨D, hd, ⟨d, _⟩⟩ | ⟨D, hd, ⟨d, _⟩⟩)
    · apply (hL R).mpr
      rw [← ProfileSubstitution.value_morphism E hE η D R d]
      exact hi ⟨D, hd, rfl⟩
    · apply (hL R).mpr
      rw [← ProfileSubstitution.value_morphism E hE η D R d]
      exact hr ⟨D, hd, rfl⟩

end Lax369799Proofs.AcceptanceObservations
