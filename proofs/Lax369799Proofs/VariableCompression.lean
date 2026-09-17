import Lax369799.VariableCompression
import Mathlib.Data.Fintype.Powerset
import Mathlib.SetTheory.Cardinal.Finite

namespace Lax369799Proofs.VariableCompression

/--
---
conclusion: Lax369799.VariableCompression.compress
---
Enumerate the image of the pair consisting of the target and observation.
Choose a preimage for every enumerated pair. Within any fixed target fibre,
the observation is injective on the selected classes.
-/
theorem compress {V : Type} [Finite V] {m n : ℕ} (σ : Fin m → Fin n) (observe : Fin m → V) :
    ∃ (m' : ℕ) (τ : Fin m → Fin m') (sectionMap : Fin m' → Fin m),
      (∀ j, τ (sectionMap j) = j) ∧
      (∀ i, σ (sectionMap (τ i)) = σ i) ∧
      (∀ i, observe (sectionMap (τ i)) = observe i) ∧
      (∀ j, Nat.card {i // σ (sectionMap i) = j} ≤ Nat.card V) := by
  classical
  let : Fintype V := Fintype.ofFinite V
  let pair := fun i => (σ i, observe i)
  let R := Set.range pair
  let e : R ≃ Fin (Fintype.card R) := Fintype.equivFin R
  let τ : Fin m → Fin (Fintype.card R) := fun i => e ⟨pair i, i, rfl⟩
  let sectionMap : Fin (Fintype.card R) → Fin m := fun j => Classical.choose (e.symm j).property
  have hs (j) : pair (sectionMap j) = (e.symm j).val := Classical.choose_spec (e.symm j).property
  have ht (j) : τ (sectionMap j) = j := by
    apply e.symm.injective
    apply Subtype.ext
    change (e.symm (e ⟨pair (sectionMap j), sectionMap j, rfl⟩)).val = _
    rw [Equiv.symm_apply_apply]
    exact hs j
  have hp (i) : pair (sectionMap (τ i)) = pair i := by
    rw [hs]
    exact congrArg Subtype.val (e.symm_apply_apply ⟨pair i, i, rfl⟩)
  refine ⟨Fintype.card R, τ, sectionMap, ht, fun i => congrArg Prod.fst (hp i),
    fun i => congrArg Prod.snd (hp i), ?_⟩
  intro j
  apply Nat.card_le_card_of_injective (fun i : {i // σ (sectionMap i) = j} => observe (sectionMap i))
  intro i i' h
  apply Subtype.ext
  have he : pair (sectionMap i.val) = pair (sectionMap i'.val) :=
    Prod.ext (i.property.trans i'.property.symm) h
  have hτ : τ (sectionMap i.val) = τ (sectionMap i'.val) := congrArg e (Subtype.ext he)
  exact (ht i.val).symm.trans (hτ.trans (ht i'.val))

end Lax369799Proofs.VariableCompression
