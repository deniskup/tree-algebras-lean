import Lax369799.SupportedSystems

/-!
---
title: Factoring out unused output variables
type: theorem
---
Every deterministic presentation is an injective renaming of a system
whose output variables all occur. Renaming a fully supported system has
full support precisely when the variable map is surjective.
-/

namespace Lax369799.SupportCompaction
open RankedSystems Renaming Resolutions

axiom compact_exists {A : RankedSet} {n : ℕ} (S : RankedSystems.System A n) :
    ∃ (m : ℕ) (σ : Fin m → Fin n) (T : SupportedSystems.System A m),
      Function.Injective σ ∧ renameSystem σ T.val = S

axiom rename_supported_iff {A : RankedSet} {m n : ℕ} (σ : Fin m → Fin n)
    (T : SupportedSystems.System A m) :
    SupportedSystems.FullySupported (renameSystem σ T.val) ↔ Function.Surjective σ

axiom rename_set_injective {A : RankedSet} {m n : ℕ} (σ : Fin m → Fin n)
    (hσ : Function.Injective σ) : Function.Injective (@Resolutions.rename A m n σ)

axiom rename_system_injective {A : RankedSet} {m n : ℕ} (σ : Fin m → Fin n)
    (hσ : Function.Injective σ) : Function.Injective (@renameSystem A m n σ)

axiom support_image {A : RankedSet} {m n : ℕ} (σ : Fin m → Fin n)
    (T : SupportedSystems.System A m) (j : Fin n) :
    (∃ v d, (renameSystem σ T.val).val.graph.edge v d (.inr j)) ↔ j ∈ Set.range σ

axiom compact_unique {A : RankedSet} {m k n : ℕ}
    (σ : Fin m → Fin n) (τ : Fin k → Fin n)
    (hσ : Function.Injective σ) (hτ : Function.Injective τ)
    (S : SupportedSystems.System A m) (T : SupportedSystems.System A k)
    (h : renameSystem σ S.val = renameSystem τ T.val) :
    ∃ e : Fin m ≃ Fin k, (∀ i, τ (e i) = σ i) ∧ renameSystem e S.val = T.val

end Lax369799.SupportCompaction
