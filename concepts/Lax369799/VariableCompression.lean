import Lax369799.Resolutions
import Mathlib.Data.Fintype.EquivFin

/-!
---
title: Compression of variable maps by finite observations
type: theorem
---
Group variables by their target and a finite observation. Choosing one
representative of each group preserves both observations and bounds each
new target fibre by the number of possible observations.
-/
namespace Lax369799.VariableCompression

axiom compress {V : Type} [Finite V] {m n : ℕ} (σ : Fin m → Fin n) (observe : Fin m → V) :
    ∃ (m' : ℕ) (τ : Fin m → Fin m') (sectionMap : Fin m' → Fin m),
      (∀ j, τ (sectionMap j) = j) ∧
      (∀ i, σ (sectionMap (τ i)) = σ i) ∧
      (∀ i, observe (sectionMap (τ i)) = observe i) ∧
      (∀ j, Nat.card {i // σ (sectionMap i) = j} ≤ Nat.card V)

end Lax369799.VariableCompression
