import Lax369799.FiniteContinuityOrder
import Lax369799Proofs.FiniteYieldContinuity

namespace Lax369799Proofs.FiniteContinuityOrder
open Lax369799.RankedSystems (RankedSet SetSystem trim)
open Lax369799.FinitePresentations Lax369799.FiniteContexts Lax369799.FiniteContextualOrder
open Lax369799.FiniteAcceptance

/--
---
conclusion: Lax369799.FiniteContinuityOrder.accepting_approximation
---
The reachable restriction covers the original presentation through the
context. Apply yield continuity to that restriction and interchange the
universal acceptance test with the finite-family union.
-/
theorem accepting_approximation {A : RankedSet} (L : Lax369799.Algebras.Language A) {k : ℕ}
    (C : Context A k 0) (S : FiniteSystem A k) :
    Accepting L (plug C S) ↔
      ∀ (m : ℕ) (F : Fin m → SetSystem A k),
        (∀ i, Lax369799.Morphisms.Yield (trim S.graph) (F i)) →
        Accepting L (plug C (ofSetSystem (Lax369799.YieldContinuity.finiteSum F))) := by
  have he := FiniteCovers.accepting_cover L
    (FiniteCovers.plugCover C (S := ofSetSystem (trim S.graph)) (T := S)
      (FiniteAcceptance.trimProjection S.graph))
  constructor
  · intro h m F hF T hT
    exact he.mpr h T ((FiniteYieldContinuity.continuity C (trim S.graph) T).mpr ⟨m, F, hF, hT⟩)
  · intro h
    apply he.mp
    intro T hT
    obtain ⟨m, F, hF, ht⟩ := (FiniteYieldContinuity.continuity C (trim S.graph) T).mp hT
    exact h m F hF T ht

/--
---
conclusion: Lax369799.FiniteContinuityOrder.order_approximation
---
Apply the acceptance approximation in every testing context. The finite
family quantifier commutes with the universal context quantifier.
-/
theorem order_approximation {A : RankedSet} (L : Lax369799.Algebras.Language A) {n : ℕ}
    (R S : FiniteSystem A n) :
    Below (Accepting L) R S ↔
      ∀ (m : ℕ) (F : Fin m → SetSystem A n),
        (∀ i, Lax369799.Morphisms.Yield (trim S.graph) (F i)) →
        Below (Accepting L) R (ofSetSystem (Lax369799.YieldContinuity.finiteSum F)) := by
  constructor
  · intro h m F hF C hC
    exact (accepting_approximation L C S).mp (h C hC) m F hF
  · intro h C hC
    exact (accepting_approximation L C S).mpr (fun m F hF => h m F hF C hC)

end Lax369799Proofs.FiniteContinuityOrder
