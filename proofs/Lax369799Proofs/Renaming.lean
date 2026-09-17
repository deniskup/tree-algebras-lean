import Lax369799.Renaming

namespace Lax369799Proofs.Renaming
open Lax369799.RankedSystems Lax369799.Morphisms Lax369799.Resolutions

/--
---
conclusion: Lax369799.Renaming.rename_identity
---
The identity variable map leaves every transition target unchanged.
-/
theorem rename_identity {A : RankedSet} {n : ℕ} (S : SetSystem A n) : rename id S = S := by
  cases S
  dsimp only [rename]
  congr 1
  congr 1
  funext v d t
  apply propext
  simp only [Sum.map_id_id, id_eq]
  constructor
  · rintro ⟨s, hs, rfl⟩; exact hs
  · intro h; exact ⟨t, h, rfl⟩

/--
---
conclusion: Lax369799.Renaming.rename_composition
---
Successive renamings compose on variable targets and leave vertex targets
unchanged. Their existential edge witnesses compose in the same way.
-/
theorem rename_composition {A : RankedSet} {m n k : ℕ}
    (σ : Fin m → Fin n) (τ : Fin n → Fin k) (S : SetSystem A m) :
    rename τ (rename σ S) = rename (τ ∘ σ) S := by
  cases S
  dsimp only [rename]
  congr 1
  congr 1
  funext v d t
  apply propext
  constructor
  · rintro ⟨u, ⟨s, hs, rfl⟩, rfl⟩
    exact ⟨s, hs, by cases s <;> rfl⟩
  · rintro ⟨s, hs, rfl⟩
    exact ⟨Sum.map id σ s, ⟨s, hs, rfl⟩, by cases s <;> rfl⟩

/--
---
conclusion: Lax369799.Renaming.rename_relabel
---
Renaming changes transition targets and relabelling changes vertex labels;
the two constructions commute definitionally.
-/
theorem rename_relabel {A B : RankedSet} (η : RankedMap A B) {m n : ℕ}
    (σ : Fin m → Fin n) (S : SetSystem A m) :
    rename σ (relabel η S) = relabel η (rename σ S) := rfl

private def renameMap {A : RankedSet} {m n : ℕ} (σ : Fin m → Fin n)
    {S T : SetSystem A m} (f : Morphism S T) : Morphism (rename σ S) (rename σ T) where
  toFun := f.toFun
  label := f.label
  initial := f.initial
  root := f.root
  edge := by
    rintro v d t ⟨s, hs, rfl⟩
    exact ⟨Sum.map f.toFun id s, f.edge v d s hs, by cases s <;> rfl⟩

/--
---
conclusion: Lax369799.Renaming.rename_morphism
---
Keep the same vertex map. To lift a renamed edge, choose its original
edge witness, lift that edge, and then rename its variable target.
-/
theorem rename_morphism {A : RankedSet} {m n : ℕ} (σ : Fin m → Fin n)
    {S T : SetSystem A m} (f : Morphism S T) :
    ∃ g : Morphism (rename σ S) (rename σ T), g.toFun = f.toFun ∧
      (f.LocallySurjective → g.LocallySurjective) := by
  refine ⟨renameMap σ f, rfl, ?_⟩
  intro hf
  refine ⟨hf.1, hf.2.1, ?_⟩
  rintro v d t ⟨s, hs, rfl⟩
  obtain ⟨u, hu, rfl⟩ := hf.2.2 v d s hs
  exact ⟨Sum.map id σ u, ⟨u, hu, rfl⟩, by cases u <;> rfl⟩

end Lax369799Proofs.Renaming
