import Lax369799.SupportedYieldContinuity
import Lax369799Proofs.SupportedYieldComparison
import Lax369799Proofs.FiniteYieldContinuity

set_option backward.isDefEq.respectTransparency false
namespace Lax369799Proofs.SupportedYieldContinuity
open Lax369799
open RankedSystems FinitePresentations FiniteContexts SupportedMorphisms SupportedYields
open Lax369799.SupportedYieldContinuity

private theorem component_yield {A : RankedSet} {n : ℕ} {S : FiniteSystem A n} (c : Component S) :
    Morphisms.Yield (trim S.graph) c.realize := by
  cases c with
  | mk m U σ b h =>
    cases b with
    | false => exact Or.inl ⟨Renaming.renameSystem σ U.val,(SupportedYieldComparison.initial_yield S U σ).mp h,rfl⟩
    | true => exact Or.inr ⟨Renaming.renameSystem σ U.val,(SupportedYieldComparison.root_yield S U σ).mp h,rfl⟩

private theorem yield_component {A : RankedSet} {n : ℕ} (S : FiniteSystem A n) (R : SetSystem A n)
    (h : Morphisms.Yield (trim S.graph) R) : ∃ c : Component S, c.realize = R := by
  rcases h with ⟨U,hU,rfl⟩ | ⟨U,hU,rfl⟩
  · obtain ⟨m,σ,V,_,hV⟩ := SupportCompaction.compact_exists U
    let c : Component S := ⟨m,V,σ,false,(SupportedYieldComparison.initial_yield S V σ).mpr (by rw [hV]; exact hU)⟩
    exact ⟨c,congrArg Subtype.val hV⟩
  · obtain ⟨m,σ,V,_,hV⟩ := SupportCompaction.compact_exists U
    let c : Component S := ⟨m,V,σ,true,(SupportedYieldComparison.root_yield S V σ).mpr (by rw [hV]; exact hU)⟩
    exact ⟨c,congrArg (fun U : System A n => RankedSystems.plant U.val) hV⟩

private theorem plug_yields {A : RankedSet} {k n : ℕ} (C : Context A k n) (S : FiniteSystem A k) :
    Morphisms.YieldEquivalent
      (trim (plug C (ofSetSystem (trim S.graph))).graph) (trim (plug C S).graph) := by
  let f := FiniteCovers.plugCover C (S := ofSetSystem (trim S.graph)) (T := S)
    (FiniteAcceptance.trimProjection S.graph)
  let g : Pullbacks.Map _ _ := ⟨f.toFun,f.initial,f.root,f.label,f.edge⟩
  exact (Yields.morphism_yields (Pullbacks.trimMap g)).2
    (Pullbacks.trimMap_surjective g f.initial_lift f.root_lift f.edge_lift)

private theorem yield_continuity {A : RankedSet} {k n : ℕ} (C : Context A k n)
    (S : FiniteSystem A k) (R : SetSystem A n) :
    Morphisms.Yield (trim (plug C S).graph) R ↔
      ∃ (m : ℕ) (F : Fin m → Component S), Morphisms.Yield (trim (plug C (realizationSum F)).graph) R := by
  classical
  constructor
  · intro h
    have hc := (plug_yields C S R).mpr h
    obtain ⟨m,F,hF,hR⟩ := (FiniteYieldContinuity.continuity C (trim S.graph) R).mp hc
    choose c he using fun i => yield_component S (F i) (hF i)
    have hfun : (fun i => (c i).realize) = F := funext he
    refine ⟨m,c,?_⟩
    change Morphisms.Yield (FiniteYieldContinuity.insert C
      (YieldContinuity.finiteSum (fun i => (c i).realize))) R
    rw [hfun]
    exact hR
  · rintro ⟨m,F,hR⟩
    have hc := (FiniteYieldContinuity.continuity C (trim S.graph) R).mpr
      ⟨m,fun i => (F i).realize,fun i => component_yield (F i),hR⟩
    exact (plug_yields C S R).mp hc

private theorem initial_iff {A : RankedSet} {n : ℕ} (S : SetSystem A n) (R : System A n) :
    Morphisms.Yield S R.val ↔ Morphisms.InitYield S R := by
  constructor
  · rintro (⟨U,hU,he⟩ | ⟨U,_,he⟩)
    · have hR : R = U := Subtype.ext he
      exact hR.symm ▸ hU
    · obtain ⟨i,hi⟩ := R.property.1
      have hr : R.val.graph.initial.Nonempty := ⟨i,by rw [hi]; rfl⟩
      have hn := (Iff.of_eq (congrArg (fun G : SetSystem A n => G.graph.initial.Nonempty) he)).mp hr
      obtain ⟨v,hv⟩ := hn
      exact hv.elim
  · intro h; exact Or.inl ⟨R,h,rfl⟩

private theorem root_iff {A : RankedSet} {n : ℕ} (S : SetSystem A n) (R : System A n) :
    Morphisms.Yield S (RankedSystems.plant R.val) ↔ Morphisms.InitYield (RankedSystems.uproot S) R := by
  constructor
  · rintro (⟨U,_,he⟩ | ⟨U,hU,he⟩)
    · obtain ⟨i,hi⟩ := U.property.1
      have hu : U.val.graph.initial.Nonempty := ⟨i,by rw [hi]; rfl⟩
      have hn := (Iff.of_eq (congrArg (fun G : SetSystem A n => G.graph.initial.Nonempty) he)).mpr hu
      obtain ⟨v,hv⟩ := hn
      exact hv.elim
    · have hR := PlantAcceptance.plant_injective R U he
      exact hR.symm ▸ hU
  · intro h; exact Or.inr ⟨R,h,rfl⟩

/--
---
conclusion: Lax369799.SupportedYieldContinuity.initial_continuity
---
Initial yields have finite support in the inserted presentation. Compact
the outputs of each component in a finite approximation, retaining its
variable map and whether it is an initial or a root yield.
-/
theorem initial_continuity {A : RankedSet} {k n r : ℕ} (C : Context A k n)
    (S : FiniteSystem A k) (U : SupportedSystems.System A r) (σ : Fin r → Fin n) :
    InitialYield (plug C S) U σ ↔
      ∃ (m : ℕ) (F : Fin m → Component S), InitialYield (plug C (realizationSum F)) U σ := by
  let R := Renaming.renameSystem σ U.val
  have hbase (S : FiniteSystem A k) : InitialYield (plug C S) U σ ↔
      Morphisms.Yield (trim (plug C S).graph) R.val :=
    (SupportedYieldComparison.initial_yield _ U σ).trans (initial_iff _ R).symm
  constructor
  · intro h
    obtain ⟨m,F,hF⟩ := (yield_continuity C S R.val).mp ((hbase S).mp h)
    exact ⟨m,F,(hbase _).mpr hF⟩
  · rintro ⟨m,F,hF⟩
    exact (hbase S).mpr ((yield_continuity C S R.val).mpr ⟨m,F,(hbase _).mp hF⟩)

/--
---
conclusion: Lax369799.SupportedYieldContinuity.root_continuity
---
Root yields have finite support in the inserted presentation. Compact
the outputs of each component in a finite approximation, retaining its
variable map and whether it is an initial or a root yield.
-/
theorem root_continuity {A : RankedSet} {k n r : ℕ} (C : Context A k n)
    (S : FiniteSystem A k) (U : SupportedSystems.System A r) (σ : Fin r → Fin n) :
    RootYield (plug C S) U σ ↔
      ∃ (m : ℕ) (F : Fin m → Component S), RootYield (plug C (realizationSum F)) U σ := by
  let R := Renaming.renameSystem σ U.val
  have hbase (S : FiniteSystem A k) : RootYield (plug C S) U σ ↔
      Morphisms.Yield (trim (plug C S).graph) (RankedSystems.plant R.val) :=
    (SupportedYieldComparison.root_yield _ U σ).trans (root_iff _ R).symm
  constructor
  · intro h
    obtain ⟨m,F,hF⟩ := (yield_continuity C S (RankedSystems.plant R.val)).mp ((hbase S).mp h)
    exact ⟨m,F,(hbase _).mpr hF⟩
  · rintro ⟨m,F,hF⟩
    exact (hbase S).mpr ((yield_continuity C S (RankedSystems.plant R.val)).mpr ⟨m,F,(hbase _).mp hF⟩)

end Lax369799Proofs.SupportedYieldContinuity
