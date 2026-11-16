import Lax369799.SupportedYields
import Lax369799Proofs.SupportedMorphisms
import Lax369799Proofs.FiniteRenaming

set_option backward.isDefEq.respectTransparency false
namespace Lax369799Proofs.SupportedYields
open Lax369799
open RankedSystems (RankedSet)
open FinitePresentations FiniteMorphisms FiniteStructureTheorems
open SupportedMorphisms FiniteRenaming SupportedYields

private def identity {A : RankedSet} {n : ℕ} (S : FiniteSystem A n) : Morphism S S where
  toFun := id
  label := fun _ => rfl
  initial := fun _ h => h
  root := fun _ h => h
  edge := by intro v d t h; cases t <;> exact h

private def identityToPush {A : RankedSet} {n : ℕ} (S : FiniteSystem A n) :
    Morphism S (push id S) where
  toFun := id
  label := fun _ => rfl
  initial := fun _ h => h
  root := fun _ h => h
  edge := fun _ _ t h => ⟨t,h,by cases t <;> rfl⟩

private def identityFromPush {A : RankedSet} {n : ℕ} (S : FiniteSystem A n) :
    Morphism (push id S) S where
  toFun := id
  label := fun _ => rfl
  initial := fun _ h => h
  root := fun _ h => h
  edge := by
    rintro v d t ⟨s,hs,rfl⟩
    cases s <;> exact hs

private theorem initial_forward {A : RankedSet} {m n : ℕ} {S T : FiniteSystem A n}
    (f : Morphism S T) (R : SupportedSystems.System A m) (σ : Fin m → Fin n)
    (h : InitialYield S R σ) : InitialYield T R σ := by
  obtain ⟨U,a,b,hb⟩ := h
  obtain ⟨c,_,_,_⟩ := FiniteStructureTheorems.composition a f
  exact ⟨U,c,b,hb⟩

private def uprootMap {A : RankedSet} {n : ℕ} {S T : FiniteSystem A n}
    (f : Morphism S T) : Morphism (uproot S) (uproot T) where
  toFun := f.toFun
  label := f.label
  initial := f.root
  root := fun _ h => h.elim
  edge := f.edge

private theorem uproot_local {A : RankedSet} {n : ℕ} {S T : FiniteSystem A n}
    (f : Morphism S T) (hf : LocallySurjective f) : LocallySurjective (uprootMap f) :=
  ⟨hf.2.1,fun _ h => h.elim,hf.2.2⟩

private theorem initial_reflect {A : RankedSet} {m n : ℕ} {S T : FiniteSystem A n}
    (f : Morphism S T) (hf : LocallySurjective f)
    (R : SupportedSystems.System A m) (σ : Fin m → Fin n)
    (h : InitialYield T R σ) : InitialYield S R σ := by
  obtain ⟨U,a,b,hb⟩ := h
  obtain ⟨a',_⟩ := (FiniteRenaming.adjunction σ (presentation U) T a.toFun).mp ⟨a,rfl⟩
  obtain ⟨f',_,hf',_⟩ := FiniteRenaming.pull_morphism σ f
  obtain ⟨P,p,q,_,_,hq,_,_,_⟩ := FiniteStructureTheorems.pullback f' a'
  obtain ⟨W,i,k,_,_,hk⟩ := SupportedMorphisms.system_selection P U q (hq (hf' hf))
  obtain ⟨c,_,_,_⟩ := FiniteStructureTheorems.composition i p
  obtain ⟨c',_⟩ := (FiniteRenaming.adjunction σ (presentation W) S c.toFun).mpr ⟨c,rfl⟩
  obtain ⟨d,_,_,hd⟩ := FiniteStructureTheorems.composition k b
  exact ⟨W,c',d,hd hk hb⟩

private theorem initial_unfold_forward {A : RankedSet} {m n : ℕ} (S : FiniteSystem A n)
    (T T' : SupportedSystems.System A m) (σ : Fin m → Fin n)
    (he : UnfoldEquivalent (presentation T) (presentation T'))
    (h : InitialYield S T σ) : InitialYield S T' σ := by
  obtain ⟨U,a,b,hb⟩ := h
  obtain ⟨D,d,d',_,hd'⟩ := SupportedMorphisms.common_system_unfolding T T' he
  obtain ⟨W,wU,wD,_,hwU,hwD,_⟩ := SupportedMorphisms.system_pullback U D T b d
  obtain ⟨w,_,_,_⟩ := FiniteRenaming.push_morphism σ wU
  obtain ⟨c,_,_,_⟩ := FiniteStructureTheorems.composition w a
  obtain ⟨e,_,_,he'⟩ := FiniteStructureTheorems.composition wD d'
  exact ⟨W,c,e,he' hwD hd'⟩

/--
---
conclusion: Lax369799.SupportedYields.unfold_invariance
---
Pull back a yield witness with a common system unfolding. Its projections
supply a new witness with exactly the original variable map. Apply the
same construction with the roots made initial for root yields.
-/
theorem unfold_invariance {A : RankedSet} {m n : ℕ} (S : FiniteSystem A n)
    (T T' : SupportedSystems.System A m) (σ : Fin m → Fin n)
    (h : UnfoldEquivalent (presentation T) (presentation T')) :
    (InitialYield S T σ ↔ InitialYield S T' σ) ∧ (RootYield S T σ ↔ RootYield S T' σ) := by
  have hr := (FiniteStructureTheorems.unfold_equivalence A m).symm h
  exact ⟨⟨initial_unfold_forward S T T' σ h,initial_unfold_forward S T' T σ hr⟩,
    ⟨initial_unfold_forward (uproot S) T T' σ h,
      initial_unfold_forward (uproot S) T' T σ hr⟩⟩

/--
---
conclusion: Lax369799.SupportedYields.morphism_yields
---
Compose a yield's renamed morphism for monotonicity. For reflection,
move the variable map across the morphism using the adjunction, pull
back the resulting locally surjective map, and select a supported system.
-/
theorem morphism_yields {A : RankedSet} {n : ℕ} {S T : FiniteSystem A n}
    (f : Morphism S T) : YieldBelow S T ∧ (LocallySurjective f → YieldEquivalent S T) := by
  refine ⟨?_,?_⟩
  · intro m R σ
    exact ⟨initial_forward f R σ,initial_forward (uprootMap f) R σ⟩
  · intro hf m R σ
    exact ⟨⟨initial_forward f R σ,initial_reflect f hf R σ⟩,
      ⟨initial_forward (uprootMap f) R σ,initial_reflect (uprootMap f) (uproot_local f hf) R σ⟩⟩

/--
---
conclusion: Lax369799.SupportedYields.unfold_yields
---
The two foldings of a common unfolding preserve and reflect both yield
families. Compose their equivalences with the variable map fixed.
-/
theorem unfold_yields {A : RankedSet} {n : ℕ} {S T : FiniteSystem A n}
    (h : UnfoldEquivalent S T) : YieldEquivalent S T := by
  obtain ⟨U,f,g,hf,hg⟩ := h
  have hS := (morphism_yields f).2 hf.1
  have hT := (morphism_yields g).2 hg.1
  intro m R σ
  exact ⟨(hS m R σ).1.symm.trans (hT m R σ).1,
    (hS m R σ).2.symm.trans (hT m R σ).2⟩

/--
---
conclusion: Lax369799.SupportedYields.system_yield_equivalence
---
Unfold-equivalence preserves all yields. Conversely the identity yield
of one system, viewed as a yield of the other, supplies a common
supported unfolding because every morphism between systems is a folding.
-/
theorem system_yield_equivalence {A : RankedSet} {n : ℕ}
    (S T : SupportedSystems.System A n) :
    UnfoldEquivalent (presentation S) (presentation T) ↔
      YieldEquivalent (presentation S) (presentation T) := by
  refine ⟨unfold_yields,?_⟩
  intro h
  have hS : InitialYield (presentation S) S id :=
    ⟨S,identityFromPush (presentation S),identity (presentation S),
      SupportedMorphisms.system_folding S S (identity (presentation S))⟩
  obtain ⟨U,a,b,hb⟩ := (h n S id).1.mp hS
  obtain ⟨c,_,_,_⟩ := FiniteStructureTheorems.composition (identityToPush (presentation U)) a
  exact ⟨presentation U,b,c,hb,SupportedMorphisms.system_folding U T c⟩

end Lax369799Proofs.SupportedYields
