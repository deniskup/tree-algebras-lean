import Lax369799.SmallProfileRefinement
import Lax369799Proofs.BoundedProfileRefinement

namespace Lax369799Proofs.SmallProfileRefinement
open Lax369799
open RankedSystems Algebras FinitePresentations

private theorem restrict_profiles {A B : RankedSet} (ρ : ∀ n, System A n → B n)
    {n : ℕ} (S T : SetSystem A n) (h : Resolutions.SmallProfile ρ S = Resolutions.SmallProfile ρ T) :
    FiniteProfiles.BoundedProfile (Nat.card (B 1) + 1) ρ S =
      FiniteProfiles.BoundedProfile (Nat.card (B 1) + 1) ρ T := by
  have forward (U V : SetSystem A n)
      (h : Resolutions.SmallProfile ρ U = Resolutions.SmallProfile ρ V) :
      FiniteProfiles.BoundedProfile (Nat.card (B 1) + 1) ρ U ⊆
        FiniteProfiles.BoundedProfile (Nat.card (B 1) + 1) ρ V := by
    rintro e ⟨he, hb⟩
    have hs : Resolutions.SmallMap B e.2.2 := by
      intro j
      have hj := hb j
      unfold Resolutions.SmallBound
      omega
    have hsmall : e ∈ Resolutions.SmallProfile ρ U := ⟨he, hs⟩
    rw [h] at hsmall
    exact ⟨hsmall.1, hb⟩
  exact Set.Subset.antisymm (forward S T h) (forward T S h.symm)

/--
---
conclusion: Lax369799.SmallProfileRefinement.refines
---
Restrict the equal small profiles to the bound |B₁| + 1. The checked
contextual refinement theorem for that bound then applies to both the
initial and root observations.
-/
theorem refines {A B : RankedSet} (E : Algebra B) (hB : RankwiseFinite B)
    (hE : UnfoldInvariant E) (η : RankedMap A B) (F : Set (B 0)) (L : Language A)
    (hL : Recognizes E η F L) {n : ℕ} (S T : FiniteSystem A n)
    (h : FiniteProfiles.SmallProfileEquivalent
      (fun k R => E.eval k (relabelSystem η R)) S T) :
    FiniteContextualOrder.Equivalent (FiniteAcceptance.Accepting L) S T := by
  let : Finite (B 1) := hB 1
  exact BoundedProfileRefinement.refines E hE η F L hL S T
    ⟨restrict_profiles _ _ _ h.1, restrict_profiles _ _ _ h.2⟩

end Lax369799Proofs.SmallProfileRefinement
