import Lax369799.SupportedYieldComparison
import Lax369799Proofs.SupportCompaction
import Lax369799Proofs.SupportedYields
import Lax369799Proofs.ResolutionLifting
import Lax369799Proofs.PlantAcceptance
import Lax369799Proofs.FiniteCovers
import Lax369799Proofs.FiniteYieldContinuity
import Lax369799Proofs.FiniteContextCongruence

set_option backward.isDefEq.respectTransparency false
namespace Lax369799Proofs.SupportedYieldComparison
open Lax369799
open RankedSystems FinitePresentations FiniteContexts
open SupportedMorphisms FiniteRenaming SupportedYields

private noncomputable def finite_resolution {A : RankedSet} {m n : ℕ} (S : FiniteSystem A n)
    (R : System A m) (σ : Fin m → Fin n)
    (r : Morphisms.Morphism (Resolutions.rename σ R.val) (trim S.graph)) :
    FiniteMorphisms.Morphism (push σ (ofSetSystem R.val)) S := by
  let f := PresentationObservations.toPresentation r
  exact ⟨f.toFun,f.initial,f.root,f.label,f.edge⟩

private noncomputable def legacy_resolution {A : RankedSet} {m n : ℕ} (S : FiniteSystem A n)
    (R : System A m) (σ : Fin m → Fin n)
    (f : FiniteMorphisms.Morphism (push σ (ofSetSystem R.val)) S) :
    Morphisms.Morphism (Resolutions.rename σ R.val) (trim S.graph) :=
  Pullbacks.lift ⟨f.toFun,f.initial,f.root,f.label,f.edge⟩

/--
---
conclusion: Lax369799.SupportedYieldComparison.initial_yield
---
Rename a supported witness in the forward direction. In the reverse
direction restore the source variables through the unfolding and lift
full support from the supported target.
-/
theorem initial_yield {A : RankedSet} {m n : ℕ} (S : FiniteSystem A n)
    (U : SupportedSystems.System A m) (σ : Fin m → Fin n) :
    InitialYield S U σ ↔ Morphisms.InitYield (trim S.graph) (Renaming.renameSystem σ U.val) := by
  constructor
  · rintro ⟨W,a,b,hb⟩
    obtain ⟨g,_,hg,_⟩ := FiniteRenaming.push_morphism σ b
    let g' : Morphisms.Morphism (Renaming.renameSystem σ W.val).val (Renaming.renameSystem σ U.val).val :=
      ⟨g.toFun,g.initial,g.root,g.label,g.edge⟩
    exact ⟨Renaming.renameSystem σ W.val,⟨legacy_resolution S W.val σ a⟩,g',hg hb.1⟩
  · rintro ⟨D,⟨d⟩,⟨f,_⟩⟩
    obtain ⟨W,hW,g,_⟩ := ResolutionLifting.rename_lift σ U.val D f
    let g' : FiniteMorphisms.Morphism (ofSetSystem W.val) (presentation U) :=
      ⟨g.toFun,g.initial,g.root,g.label,g.edge⟩
    let W' : SupportedSystems.System A m := ⟨W,SupportedMorphisms.source_support W U g'⟩
    have r : Morphisms.Morphism (Resolutions.rename σ W.val) (trim S.graph) := by
      rw [show Resolutions.rename σ W.val = D.val from hW]
      exact d
    exact ⟨W',finite_resolution S W σ r,g',SupportedMorphisms.system_folding W' U g'⟩

/--
---
conclusion: Lax369799.SupportedYieldComparison.root_yield
---
The canonical trimming cover preserves root entries and edges. Transfer
the initial-yield comparison across its rooted cover.
-/
theorem root_yield {A : RankedSet} {m n : ℕ} (S : FiniteSystem A n)
    (U : SupportedSystems.System A m) (σ : Fin m → Fin n) :
    RootYield S U σ ↔ Morphisms.InitYield (RankedSystems.uproot (trim S.graph)) (Renaming.renameSystem σ U.val) := by
  let f := PresentationObservations.rootedCover (FiniteAcceptance.trimProjection S.graph)
  let g : Pullbacks.Map _ _ := ⟨f.toFun,f.initial,f.root,f.label,f.edge⟩
  have hc := Pullbacks.trimMap_surjective g f.initial_lift f.root_lift f.edge_lift
  have he := (Yields.morphism_yields (Pullbacks.trimMap g)).2 hc
  have hi : Morphisms.InitYield (RankedSystems.uproot (trim S.graph)) (Renaming.renameSystem σ U.val) ↔
      Morphisms.InitYield (trim (SupportedYields.uproot S).graph) (Renaming.renameSystem σ U.val) :=
    ⟨ResolutionLifting.initial_mono (fun R h => (he R).mp h) _,
      ResolutionLifting.initial_mono (fun R h => (he R).mpr h) _⟩
  exact (initial_yield (SupportedYields.uproot S) U σ).trans hi.symm

/--
---
conclusion: Lax369799.SupportedYieldComparison.legacy_below
---
Compact unused outputs of each legacy yield, retaining its variable
map. Conversely instantiate the supported yield test on renamed systems;
initial and planted root yields remain separate.
-/
theorem legacy_below {A : RankedSet} {n : ℕ} (S T : FiniteSystem A n) :
    YieldBelow S T ↔ Morphisms.YieldBelow (trim S.graph) (trim T.graph) := by
  constructor
  · intro h X hX
    rcases hX with ⟨R,hR,rfl⟩ | ⟨R,hR,rfl⟩
    · obtain ⟨k,ι,U,_,hU⟩ := SupportCompaction.compact_exists R
      have hr := (initial_yield S U ι).mpr (by rw [hU]; exact hR)
      have ht := (initial_yield T U ι).mp ((h k U ι).1 hr)
      rw [hU] at ht
      exact Or.inl ⟨R,ht,rfl⟩
    · obtain ⟨k,ι,U,_,hU⟩ := SupportCompaction.compact_exists R
      have hr := (root_yield S U ι).mpr (by rw [hU]; exact hR)
      have ht := (root_yield T U ι).mp ((h k U ι).2 hr)
      rw [hU] at ht
      exact Or.inr ⟨R,ht,rfl⟩
  · intro h m U σ
    refine ⟨?_,?_⟩
    · intro hu
      exact (initial_yield T U σ).mpr (ResolutionLifting.initial_mono h _ ((initial_yield S U σ).mp hu))
    · intro hu
      let R := Renaming.renameSystem σ U.val
      have hy := h (RankedSystems.plant R.val) (Or.inr ⟨R,(root_yield S U σ).mp hu,rfl⟩)
      rcases hy with ⟨V,_,he⟩ | ⟨V,hv,he⟩
      · obtain ⟨i,hi⟩ := V.property.1
        have hv : (V.val.graph.initial).Nonempty := ⟨i,by rw [hi]; rfl⟩
        have hn := (Iff.of_eq (congrArg (fun G : SetSystem A n => G.graph.initial.Nonempty) he)).mpr hv
        obtain ⟨v,hv⟩ := hn
        exact hv.elim
      · have hRV : R = V := PlantAcceptance.plant_injective R V he
        exact (root_yield T U σ).mpr (by change Morphisms.InitYield _ R; rw [hRV]; exact hv)

private theorem plug_yields {A : RankedSet} {k n : ℕ} (C : Context A k n) (S : FiniteSystem A k) :
    Morphisms.YieldEquivalent
      (trim (plug C (ofSetSystem (trim S.graph))).graph) (trim (plug C S).graph) := by
  let f := FiniteCovers.plugCover C (S := ofSetSystem (trim S.graph)) (T := S) (FiniteAcceptance.trimProjection S.graph)
  let g : Pullbacks.Map _ _ := ⟨f.toFun,f.initial,f.root,f.label,f.edge⟩
  exact (Yields.morphism_yields (Pullbacks.trimMap g)).2
    (Pullbacks.trimMap_surjective g f.initial_lift f.root_lift f.edge_lift)

/--
---
conclusion: Lax369799.SupportedYieldComparison.context_mono
---
Transfer the yield comparison to reachable presentations, apply finite
context monotonicity, then restore the original unpruned presentations
through their substitution covers.
-/
theorem context_mono {A : RankedSet} {k n : ℕ} (C : Context A k n)
    (S T : FiniteSystem A k) (h : YieldBelow S T) : YieldBelow (plug C S) (plug C T) := by
  apply (legacy_below _ _).mpr
  have hs := plug_yields C S
  have ht := plug_yields C T
  have hC := FiniteYieldContinuity.context_mono C (trim S.graph) (trim T.graph) ((legacy_below S T).mp h)
  intro R hr
  exact (ht R).mp (hC R ((hs R).mpr hr))

/--
---
conclusion: Lax369799.SupportedYieldComparison.yield_order
---
Yield inclusion reverses universal yield acceptance in every closed
context. Canonical substitution covers identify each unpruned
presentation with its reachable representative (Lemma 73).
-/
theorem yield_order {A : RankedSet} (L : Algebras.Language A) {n : ℕ}
    (S T : FiniteSystem A n) (h : YieldBelow S T) :
    FiniteContextualOrder.Below (FiniteAcceptance.Accepting L) T S := by
  have hs := FiniteCovers.contextual_cover L (S := ofSetSystem (trim S.graph)) (T := S) (FiniteAcceptance.trimProjection S.graph)
  have ht := FiniteCovers.contextual_cover L (S := ofSetSystem (trim T.graph)) (T := T) (FiniteAcceptance.trimProjection T.graph)
  have hC : FiniteContextualOrder.Below (FiniteAcceptance.Accepting L)
      (ofSetSystem (trim T.graph)) (ofSetSystem (trim S.graph)) := by
    intro C hT R hR
    exact hT R ((FiniteYieldContinuity.context_mono C (trim S.graph) (trim T.graph)
      ((legacy_below S T).mp h)) R hR)
  exact fun C hT => hs.1 C (hC C (ht.2 C hT))

/--
---
conclusion: Lax369799.SupportedYieldComparison.flatten_mono
---
Apply the generic context/substitution equivalence to yield inclusion.
Context monotonicity and composition of yield inclusions supply its
hypotheses (Corollary 48, inclusion clause).
-/
theorem flatten_mono {A : RankedSet} {n : ℕ} (P : FiniteSystem (FiniteSystem A) n)
    (Q : ∀ v, FiniteSystem A (P.graph.label v).1) (h : ∀ v, YieldBelow (Inner P.graph v) (Q v)) :
    YieldBelow (flatten P) (flatten (withLabels P Q)) := by
  let R : FiniteContextCongruence.RelationFamily A := fun _ => YieldBelow
  have hrefl : ∀ n (S : FiniteSystem A n), R n S S := by
    intro n S m U σ; exact ⟨id,id⟩
  have htrans : ∀ n (S T U : FiniteSystem A n), R n S T → R n T U → R n S U := by
    intro n S T U hST hTU m W σ
    exact ⟨fun h => (hTU m W σ).1 ((hST m W σ).1 h),
      fun h => (hTU m W σ).2 ((hST m W σ).2 h)⟩
  have hiso : ∀ n (S T : FiniteSystem A n), Isomorphic S T → R n S T := by
    rintro n S T ⟨f⟩
    let g : FiniteMorphisms.Morphism S T :=
      ⟨f.vertex,(fun v => (f.initial v).mpr),(fun v => (f.root v).mpr),f.label,(fun v d t => (f.edge v d t).mpr)⟩
    exact (SupportedYields.morphism_yields g).1
  have hs := (FiniteContextCongruence.context_iff_substitution R R hrefl hrefl htrans hiso).mp
    (fun _ _ C S T h => context_mono C S T h)
  have hp := hs (FiniteSystem A) n P (fun v => Inner P.graph v) Q h
  have he : withLabels P (fun v => Inner P.graph v) = P := by cases P; rfl
  rw [he] at hp
  exact hp


private theorem equivalent_iff_below {A : RankedSet} {n : ℕ} (S T : FiniteSystem A n) :
    YieldEquivalent S T ↔ YieldBelow S T ∧ YieldBelow T S := by
  constructor
  · intro h
    exact ⟨fun m U σ => ⟨(h m U σ).1.mp,(h m U σ).2.mp⟩,
      fun m U σ => ⟨(h m U σ).1.mpr,(h m U σ).2.mpr⟩⟩
  · rintro ⟨h,g⟩ m U σ
    exact ⟨⟨(h m U σ).1,(g m U σ).1⟩,⟨(h m U σ).2,(g m U σ).2⟩⟩

/--
---
conclusion: Lax369799.SupportedYieldComparison.flatten_congruence
---
Apply substitution monotonicity to both directions of the local yield
equivalences (Corollary 48, equivalence clause).
-/
theorem flatten_congruence {A : RankedSet} {n : ℕ} (P : FiniteSystem (FiniteSystem A) n)
    (Q : ∀ v, FiniteSystem A (P.graph.label v).1) (h : ∀ v, YieldEquivalent (Inner P.graph v) (Q v)) :
    YieldEquivalent (flatten P) (flatten (withLabels P Q)) := by
  have hf := flatten_mono P Q (fun v => ((equivalent_iff_below _ _).mp (h v)).1)
  have hb := flatten_mono (withLabels P Q) (fun v => Inner P.graph v)
    (fun v => ((equivalent_iff_below _ _).mp (h v)).2)
  have he : withLabels (withLabels P Q) (fun v => Inner P.graph v) = P := by cases P; rfl
  rw [he] at hb
  exact (equivalent_iff_below _ _).mpr ⟨hf,hb⟩

end Lax369799Proofs.SupportedYieldComparison
