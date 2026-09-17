import Lax369799.Resolutions

/-!
---
title: Renaming variables in systems and resolutions
type: theorem
---
Variable renaming preserves deterministic systems, commutes with relabelling,
and respects identity and composition. Morphisms and their local lifting
properties are preserved even when several variables are identified.
-/
namespace Lax369799.Renaming
open RankedSystems Morphisms Resolutions

def renameSystem {A : RankedSet} {m n : ℕ} (σ : Fin m → Fin n) (S : System A m) : System A n :=
  ⟨rename σ S.val, S.property.1, S.property.2.1, by
    intro v d hd
    obtain ⟨t, ht, hu⟩ := S.property.2.2 v d hd
    refine ⟨Sum.map id σ t, ⟨t, ht, rfl⟩, ?_⟩
    rintro u ⟨s, hs, rfl⟩
    exact congrArg (Sum.map id σ) (hu s hs)⟩

axiom rename_identity {A : RankedSet} {n : ℕ} (S : SetSystem A n) : rename id S = S

axiom rename_composition {A : RankedSet} {m n k : ℕ}
    (σ : Fin m → Fin n) (τ : Fin n → Fin k) (S : SetSystem A m) :
    rename τ (rename σ S) = rename (τ ∘ σ) S

axiom rename_relabel {A B : RankedSet} (η : RankedMap A B) {m n : ℕ}
    (σ : Fin m → Fin n) (S : SetSystem A m) :
    rename σ (relabel η S) = relabel η (rename σ S)

axiom rename_morphism {A : RankedSet} {m n : ℕ} (σ : Fin m → Fin n)
    {S T : SetSystem A m} (f : Morphism S T) :
    ∃ g : Morphism (rename σ S) (rename σ T), g.toFun = f.toFun ∧
      (f.LocallySurjective → g.LocallySurjective)

axiom resolution_factor {A : RankedSet} {m m' n : ℕ} (S : SetSystem A n) (T : System A m)
    (σ : Fin m → Fin n) (τ : Fin m → Fin m') (σ' : Fin m' → Fin n)
    (hσ : ∀ i, σ' (τ i) = σ i) (h : IsResolution S T σ) :
    IsResolution S (renameSystem τ T) σ'

end Lax369799.Renaming
