import Lax369799.FiniteProfiles
import Lax369799Proofs.FiniteCovers
import Lax369799Proofs.Profiles

namespace Lax369799Proofs.FiniteProfiles
open Lax369799.RankedSystems (RankedSet RankwiseFinite)
open Lax369799.FinitePresentations Lax369799.FiniteContextualOrder Lax369799.FiniteAcceptance
open Lax369799.FiniteProfiles

/--
---
conclusion: Lax369799.FiniteProfiles.small_profile_finite
---
Map a profile class to the class of its reachable restriction. This map
is injective, and the bounded-profile quotient of reachable systems is
finite by the finite-entry counting argument.
-/
theorem small_profile_finite {A B : RankedSet} (hB : RankwiseFinite B)
    (ρ : ∀ n, Lax369799.RankedSystems.System A n → B n) (n : ℕ) :
    Finite (Quot (@SmallProfileEquivalent A B ρ n)) := by
  let r := @Lax369799.Resolutions.SmallProfileEquivalent A B ρ n
  let st : Setoid (Lax369799.RankedSystems.SetSystem A n) := {
    r := r
    iseqv := ⟨fun _ => ⟨rfl, rfl⟩, fun h => ⟨h.1.symm, h.2.symm⟩,
      fun h h' => ⟨h.1.trans h'.1, h.2.trans h'.2⟩⟩ }
  let : Finite (Quot r) := Profiles.small_profile_finite hB ρ n
  let f : Quot (@SmallProfileEquivalent A B ρ n) → Quot r :=
    Quot.lift (fun S => Quot.mk r (Lax369799.RankedSystems.trim S.graph))
      (fun _ _ h => Quot.sound h)
  apply Finite.of_injective f
  intro x y h
  induction x using Quot.inductionOn with
  | h S =>
    induction y using Quot.inductionOn with
    | h T =>
      exact Quot.sound (@Quotient.exact _ st _ _ h)

/--
---
conclusion: Lax369799.FiniteProfiles.reachable_representative
---
Restrict a presentation representative to its reachable vertices. The
restriction covers the original presentation, so substitution into any
fixed context preserves the acceptance test.
-/
theorem reachable_representative {A : RankedSet} (L : Lax369799.Algebras.Language A) {n : ℕ}
    (a : Carrier (Accepting L) n) :
    ∃ S : Lax369799.RankedSystems.SetSystem A n, quotientMap (Accepting L) n (ofSetSystem S) = a := by
  induction a using Quot.inductionOn with
  | h S =>
    exact ⟨Lax369799.RankedSystems.trim S.graph,
      Quot.sound (FiniteCovers.contextual_cover L (FiniteAcceptance.trimProjection S.graph))⟩

end Lax369799Proofs.FiniteProfiles
