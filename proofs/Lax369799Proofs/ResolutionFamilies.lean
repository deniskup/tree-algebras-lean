import Lax369799.ResolutionFamilies
import Lax369799Proofs.BoundedProfiles

namespace Lax369799Proofs.ResolutionFamilies
open Lax369799.RankedSystems Lax369799.Resolutions Lax369799.FiniteProfiles
open Lax369799.ResolutionFamilies

/--
---
conclusion: Lax369799.ResolutionFamilies.finite_family
---
Choose one witnessing resolution for each bounded profile entry. The
entry type is finite, and summing the fibre bounds controls its arity.
-/
theorem finite_family {A B : RankedSet} (hB : RankwiseFinite B) (bound : ℕ)
    (ρ : ∀ n, System A n → B n) {n : ℕ} (S : SetSystem A n) :
    ∃ (k : ℕ) (w : Fin k → Witness S),
      (∀ i, (w i).arity ≤ n * bound) ∧
      BoundedProfile bound ρ S = Set.range (fun i => (w i).entry ρ) := by
  classical
  let I := {e : ProfileEntry B n // e ∈ BoundedProfile bound ρ S}
  let : Finite (BoundedProfiles.BoundedEntry B bound n) := BoundedProfiles.small_entry_finite hB bound n
  have hi : Finite I := Finite.of_injective
    (fun e : I => (⟨e.val, e.property.2⟩ : BoundedProfiles.BoundedEntry B bound n))
    (fun _ _ h => Subtype.ext (congrArg (fun a : BoundedProfiles.BoundedEntry B bound n => a.val) h))
  let : Fintype I := Fintype.ofFinite I
  let e := Fintype.equivFin I
  have hw (i : I) : ∃ w : Witness S, w.entry ρ = i.val := by
    obtain ⟨T, ht, hv⟩ := i.property.1
    exact ⟨⟨i.val.1, T, i.val.2.2, ht⟩, by change (⟨i.val.1, ρ i.val.1 T, i.val.2.2⟩ : ProfileEntry B n) = i.val; rw [hv]⟩
  choose w hw using hw
  refine ⟨Fintype.card I, fun j => w (e.symm j), ?_, ?_⟩
  · intro j
    have h := (e.symm j).property.2
    have he := hw (e.symm j)
    have hr := congrArg Sigma.fst he
    rw [show (w (e.symm j)).arity = (e.symm j).val.1 from hr]
    exact BoundedProfiles.small_rank_bound _ h
  · ext b
    constructor
    · intro hb
      refine ⟨e ⟨b, hb⟩, ?_⟩
      simpa only [Equiv.symm_apply_apply] using hw ⟨b, hb⟩
    · rintro ⟨j, rfl⟩
      change (w (e.symm j)).entry ρ ∈ BoundedProfile bound ρ S
      rw [hw]
      exact (e.symm j).property

end Lax369799Proofs.ResolutionFamilies
