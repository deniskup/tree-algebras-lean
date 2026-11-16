import Lax369799.FiniteRenaming

set_option backward.isDefEq.respectTransparency false
namespace Lax369799Proofs.FiniteRenaming
open Lax369799.RankedSystems (RankedSet)
open Lax369799.FinitePresentations Lax369799.FiniteMorphisms
open Lax369799.FiniteStructureTheorems Lax369799.FiniteRenaming

private def toPull {A : RankedSet} {m n : ℕ} (σ : Fin m → Fin n)
    {S : FiniteSystem A m} {T : FiniteSystem A n} (f : Morphism (push σ S) T) :
    Morphism S (pull σ T) where
  toFun := f.toFun
  initial := f.initial
  root := f.root
  label := f.label
  edge := by
    intro v d t ht
    have h := f.edge v d _ ⟨t,ht,rfl⟩
    cases t <;> exact h

private def fromPull {A : RankedSet} {m n : ℕ} (σ : Fin m → Fin n)
    {S : FiniteSystem A m} {T : FiniteSystem A n} (f : Morphism S (pull σ T)) :
    Morphism (push σ S) T where
  toFun := f.toFun
  initial := f.initial
  root := f.root
  label := f.label
  edge := by
    rintro v d t ⟨s,hs,rfl⟩
    have h := f.edge v d s hs
    cases s <;> exact h

/--
---
conclusion: Lax369799.FiniteRenaming.adjunction
---
The same vertex map works in both directions: moving the variable map
across the morphism changes exactly the variable targets of its edges.
-/
theorem adjunction {A : RankedSet} {m n : ℕ} (σ : Fin m → Fin n)
    (S : FiniteSystem A m) (T : FiniteSystem A n) (ρ : S.Vertex → T.Vertex) :
    (∃ f : Morphism (push σ S) T, f.toFun = ρ) ↔
      (∃ g : Morphism S (pull σ T), g.toFun = ρ) := by
  constructor
  · rintro ⟨f,hf⟩; exact ⟨toPull σ f,hf⟩
  · rintro ⟨f,hf⟩; exact ⟨fromPull σ f,hf⟩

private def pushMap {A : RankedSet} {m n : ℕ} (σ : Fin m → Fin n)
    {S T : FiniteSystem A m} (f : Morphism S T) : Morphism (push σ S) (push σ T) where
  toFun := f.toFun
  initial := f.initial
  root := f.root
  label := f.label
  edge := by
    rintro v d t ⟨s,hs,rfl⟩
    exact ⟨Sum.map f.toFun id s,f.edge v d s hs,by cases s <;> rfl⟩

private def pullMap {A : RankedSet} {m n : ℕ} (σ : Fin m → Fin n)
    {S T : FiniteSystem A n} (f : Morphism S T) : Morphism (pull σ S) (pull σ T) where
  toFun := f.toFun
  initial := f.initial
  root := f.root
  label := f.label
  edge := by
    intro v d t ht
    have h := f.edge v d _ ht
    cases t <;> exact h

/--
---
conclusion: Lax369799.FiniteRenaming.push_morphism
---
Rename the original edge witnesses after lifting them. The vertex map
and its global surjectivity are unchanged.
-/
theorem push_morphism {A : RankedSet} {m n : ℕ} (σ : Fin m → Fin n)
    {S T : FiniteSystem A m} (f : Morphism S T) :
    ∃ g : Morphism (push σ S) (push σ T), g.toFun = f.toFun ∧
      (LocallySurjective f → LocallySurjective g) ∧ (Folding f → Folding g) := by
  have hl (hf : LocallySurjective f) : LocallySurjective (pushMap σ f) := by
    refine ⟨hf.1,hf.2.1,?_⟩
    rintro v d t ⟨s,hs,rfl⟩
    obtain ⟨u,hu,rfl⟩ := hf.2.2 v d s hs
    exact ⟨Sum.map id σ u,⟨u,hu,rfl⟩,by cases u <;> rfl⟩
  exact ⟨pushMap σ f,rfl,hl,fun hf => ⟨hl hf.1,hf.2⟩⟩

/--
---
conclusion: Lax369799.FiniteRenaming.pull_morphism
---
Lift an original target edge and restore its requested source variable.
Variables are fixed by a morphism, so the restored edge has the same
variable name as the requested inverse-image edge.
-/
theorem pull_morphism {A : RankedSet} {m n : ℕ} (σ : Fin m → Fin n)
    {S T : FiniteSystem A n} (f : Morphism S T) :
    ∃ g : Morphism (pull σ S) (pull σ T), g.toFun = f.toFun ∧
      (LocallySurjective f → LocallySurjective g) ∧ (Folding f → Folding g) := by
  have hl (hf : LocallySurjective f) : LocallySurjective (pullMap σ f) := by
    refine ⟨hf.1,hf.2.1,?_⟩
    intro v d t ht
    obtain ⟨s,hs,he⟩ := hf.2.2 v d _ ht
    cases t with
    | inl w =>
      cases s with
      | inl u => exact ⟨.inl u,hs,congrArg Sum.inl (Sum.inl.inj he)⟩
      | inr i => cases he
    | inr j =>
      cases s with
      | inl u => cases he
      | inr i =>
        have hi : i = σ j := Sum.inr.inj he
        exact ⟨.inr j,by change S.graph.edge v d (.inr (σ j)); rw [←hi]; exact hs,rfl⟩
  exact ⟨pullMap σ f,rfl,hl,fun hf => ⟨hl hf.1,hf.2⟩⟩

/--
---
conclusion: Lax369799.FiniteRenaming.pull_flatten
---
Inverse variable renaming changes only external exit targets. It therefore
commutes with substitution while retaining the same flattened vertices.
-/
theorem pull_flatten {A : RankedSet} {m n : ℕ} (σ : Fin m → Fin n)
    (P : FiniteSystem (FiniteSystem A) n) : pull σ (flatten P) = flatten (pull σ P) := by
  cases P with
  | mk size G =>
    dsimp only [pull,flatten,enumerate,reindex,flattenPresentation]
    congr 1
    congr 1
    funext v d t
    apply propext
    cases t <;> simp


end Lax369799Proofs.FiniteRenaming
