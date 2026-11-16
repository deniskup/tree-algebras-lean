import Lax369799.SupportedMorphisms
import Lax369799Proofs.FiniteStructureTheorems
import Lax369799Proofs.Yields
import Lax369799Proofs.ResolutionLifting
import Lax369799Proofs.PresentationCovers

set_option backward.isDefEq.respectTransparency false
namespace Lax369799Proofs.SupportedMorphisms
open Lax369799
open RankedSystems (RankedSet Presentation trim)
open FinitePresentations FiniteMorphisms FiniteStructureTheorems SupportedMorphisms

private theorem finite_morphism_ext {A : RankedSet} {n : ℕ} {S T : FiniteSystem A n}
    (f g : Morphism S T) (h : f.toFun = g.toFun) : f = g := by
  cases f; cases g; cases h; rfl

private def legacy {A : RankedSet} {n : ℕ} (S T : RankedSystems.System A n)
    (f : Morphism (ofSetSystem S.val) (ofSetSystem T.val)) : Morphisms.Morphism S.val T.val :=
  ⟨f.toFun,f.initial,f.root,f.label,f.edge⟩

private theorem deterministic_folding {A : RankedSet} {n : ℕ}
    (S T : RankedSystems.System A n)
    (f : Morphism (ofSetSystem S.val) (ofSetSystem T.val)) : Folding f := by
  have hf := MorphismTheorems.system_morphism_locally_surjective S T (legacy S T f)
  let hc : PresentationCovers.Cover S.val.graph T.val.graph :=
    ⟨f.toFun,f.label,f.initial,f.root,f.edge,hf.1,hf.2.1,hf.2.2⟩
  exact ⟨hf,PresentationCovers.surjective_of_reachable hc T.val.reachable⟩

/--
---
conclusion: Lax369799.SupportedMorphisms.source_support
---
A morphism between deterministic systems lifts every vertex and every
outgoing edge of the target, hence every target output as well.
-/
theorem source_support {A : RankedSet} {n : ℕ}
    (S : RankedSystems.System A n) (T : SupportedSystems.System A n)
    (f : Morphism (ofSetSystem S.val) (presentation T)) : SupportedSystems.FullySupported S := by
  have hf := deterministic_folding S T.val f
  intro j
  obtain ⟨w,d,hw⟩ := T.property j
  obtain ⟨v,rfl⟩ := hf.2 w
  obtain ⟨t,ht,he⟩ := hf.1.2.2 v d (.inr j) hw
  cases t with
  | inl w => cases he
  | inr i => cases Sum.inr.inj he; exact ⟨v,d,ht⟩

/--
---
conclusion: Lax369799.SupportedMorphisms.system_folding
---
Uniqueness of the initial vertex and of successors implies local
surjectivity. Reachability of all target vertices implies surjectivity.
-/
theorem system_folding {A : RankedSet} {n : ℕ} (S T : SupportedSystems.System A n)
    (f : Morphism (presentation S) (presentation T)) : Folding f :=
  deterministic_folding S.val T.val f

/--
---
conclusion: Lax369799.SupportedMorphisms.system_selection
---
Choose one initial vertex and one edge in each permitted direction,
then restrict to the reachable part. The resulting map into the source
is injective. Its composite to the target is a folding, which also lifts
every output variable and proves full support.
-/
theorem system_selection {A : RankedSet} {n : ℕ} (S : FiniteSystem A n)
    (T : SupportedSystems.System A n) (f : Morphism S (presentation T))
    (hf : LocallySurjective f) :
    ∃ (U : SupportedSystems.System A n) (i : Morphism (presentation U) S)
      (g : Morphism (presentation U) (presentation T)),
      Function.Injective i.toFun ∧ g.toFun = f.toFun ∘ i.toFun ∧ Folding g := by
  classical
  obtain ⟨t,ht⟩ := T.val.property.1
  obtain ⟨r,hr,_⟩ := hf.1 t (by change T.val.val.graph.initial t; rw [ht]; rfl)
  have edges : ∀ v d, d < (S.graph.label v).1 → ∃ s, S.graph.edge v d s := by
    intro v d hd
    obtain ⟨s,hs,_⟩ := T.val.property.2.2 (f.toFun v) d (by change d < ((presentation T).graph.label (f.toFun v)).1; rw [f.label v]; exact hd)
    obtain ⟨u,hu,_⟩ := hf.2.2 v d s hs
    exact ⟨u,hu⟩
  let chosen (v : S.Vertex) (d : ℕ) (h : d < (S.graph.label v).1) :=
    Classical.choose (edges v d h)
  let G : Presentation A n S.Vertex := {
    label := S.graph.label, initial := {r}, root := ∅
    edge := fun v d s => ∃ h : d < (S.graph.label v).1, s = chosen v d h
    direction_valid := fun _ _ _ h => h.choose }
  have det : (trim G).Deterministic := Yields.trim_deterministic G r rfl rfl (by
    intro v d hd
    refine ⟨chosen v d hd, ⟨hd,rfl⟩, ?_⟩
    rintro s ⟨h,rfl⟩; rfl)
  let U : RankedSystems.System A n := ⟨trim G,det⟩
  let i : Morphism (ofSetSystem U.val) S := {
    toFun := Pullbacks.vertex G
    label := fun _ => rfl
    initial := by
      intro v hv
      change Pullbacks.vertex G (by exact v) = r at hv
      change S.graph.initial (Pullbacks.vertex G (by exact v))
      rw [hv]; exact hr
    root := fun _ h => h.elim
    edge := by
      rintro v d s ⟨h,he⟩
      let v' : (trim G).Vertex := v
      let s' : (trim G).Vertex ⊕ Fin n := s
      have he' : Sum.map (Pullbacks.vertex G) id s' = chosen (Pullbacks.vertex G v') d h := he
      exact (congrArg (S.graph.edge (Pullbacks.vertex G v') d) he').mpr
        (Classical.choose_spec (edges _ _ h)) }
  let g : Morphism (ofSetSystem U.val) (presentation T) := {
    toFun := f.toFun ∘ i.toFun
    initial := fun v h => f.initial _ (i.initial v h)
    root := fun v h => f.root _ (i.root v h)
    label := fun v => (f.label _).trans (i.label v)
    edge := by
      intro v d s h
      have hh := f.edge _ d _ (i.edge v d s h)
      cases s <;> exact hh }
  exact ⟨⟨U,source_support U T g⟩,i,g,Pullbacks.vertex_injective G,rfl,
    deterministic_folding U T.val g⟩

/--
---
conclusion: Lax369799.SupportedMorphisms.common_system_unfolding
---
Select a system inside the common finite unfolding. Both composites
are morphisms between supported systems and hence are foldings.
-/
theorem common_system_unfolding {A : RankedSet} {n : ℕ}
    (S T : SupportedSystems.System A n)
    (h : UnfoldEquivalent (presentation S) (presentation T)) :
    ∃ (U : SupportedSystems.System A n) (f : Morphism (presentation U) (presentation S))
      (g : Morphism (presentation U) (presentation T)), Folding f ∧ Folding g := by
  obtain ⟨P,p,q,hp,_⟩ := h
  obtain ⟨U,i,f,_,_,hf⟩ := system_selection P S p hp.1
  obtain ⟨g,_,_,_⟩ := FiniteStructureTheorems.composition i q
  exact ⟨U,f,g,hf,system_folding U T g⟩

/--
---
conclusion: Lax369799.SupportedMorphisms.rename_lift
---
The restored variable at an exit is determined by the original target.
The lifted morphism onto the fully supported target lifts each of its
outputs, so the restored presentation also has full support.
-/
theorem rename_lift {A : RankedSet} {m n : ℕ} (σ : Fin m → Fin n)
    (hσ : Function.Surjective σ) (S : SupportedSystems.System A m)
    (R : SupportedSystems.System A n)
    (f : Morphisms.Morphism R.val.val (Resolutions.rename σ S.val.val)) :
    ∃ U : SupportedSystems.System A m,
      SupportedSystems.rename σ hσ U = R ∧ Morphisms.UnfoldsTo S.val.val U.val.val := by
  obtain ⟨U,hU,g,hg⟩ := ResolutionLifting.rename_lift σ S.val R.val f
  let g' : Morphism (ofSetSystem U.val) (presentation S) :=
    ⟨g.toFun,g.initial,g.root,g.label,g.edge⟩
  refine ⟨⟨U,source_support U S g'⟩, ?_,g,hg⟩
  apply Subtype.ext
  apply Subtype.ext
  exact hU

private theorem fiber_target_inj {A : RankedSet} {n : ℕ} {S T U : FiniteSystem A n}
    (f : Morphism S U) (g : Morphism T U)
    (s t : FiniteStructureTheorems.Fiber f g ⊕ Fin n)
    (h₁ : Sum.map (fun w => w.val.1) id s = Sum.map (fun w => w.val.1) id t)
    (h₂ : Sum.map (fun w => w.val.2) id s = Sum.map (fun w => w.val.2) id t) : s = t := by
  cases s with
  | inl s =>
    cases t with
    | inl t => exact congrArg Sum.inl (Subtype.ext (Prod.ext (Sum.inl.inj h₁) (Sum.inl.inj h₂)))
    | inr j => cases h₁
  | inr i =>
    cases t with
    | inl t => cases h₁
    | inr j => exact congrArg Sum.inr (Sum.inr.inj h₁)

private theorem fiber_deterministic {A : RankedSet} {n : ℕ}
    (S T U : SupportedSystems.System A n)
    (f : Morphism (presentation S) (presentation U))
    (g : Morphism (presentation T) (presentation U)) :
    (trim (FiniteStructureTheorems.graph f g)).Deterministic := by
  classical
  let G := FiniteStructureTheorems.graph f g
  obtain ⟨s,hs⟩ := S.val.property.1
  obtain ⟨t,ht⟩ := T.val.property.1
  obtain ⟨u,hu⟩ := U.val.property.1
  have hfs := f.initial s (by change S.val.val.graph.initial s; rw [hs]; rfl)
  have hgt := g.initial t (by change T.val.val.graph.initial t; rw [ht]; rfl)
  change U.val.val.graph.initial (f.toFun s) at hfs
  change U.val.val.graph.initial (g.toFun t) at hgt
  rw [hu] at hfs hgt
  let r : FiniteStructureTheorems.Fiber f g := ⟨(s,t),hfs.trans hgt.symm⟩
  apply Yields.trim_deterministic G r
  · ext v
    constructor
    · rintro ⟨hv,hw⟩
      change S.val.val.graph.initial v.val.1 at hv
      change T.val.val.graph.initial v.val.2 at hw
      rw [hs] at hv
      rw [ht] at hw
      exact Subtype.ext (Prod.ext hv hw)
    · rintro rfl
      exact ⟨by change S.val.val.graph.initial s; rw [hs]; rfl,
        by change T.val.val.graph.initial t; rw [ht]; rfl⟩
  · ext v
    constructor
    · intro hv
      have hh := hv.1
      change S.val.val.graph.root v.val.1 at hh
      rw [S.val.property.2.1] at hh
      exact hh.elim
    · intro h; exact h.elim
  · intro v d hd
    obtain ⟨a,ha,_⟩ := S.val.property.2.2 v.val.1 d hd
    have hl : (presentation T).graph.label v.val.2 = (presentation S).graph.label v.val.1 :=
      (g.label _).symm.trans ((congrArg (presentation U).graph.label v.property.symm).trans (f.label _))
    have hdt : d < (T.val.val.graph.label v.val.2).1 := by
      change d < ((presentation T).graph.label v.val.2).1
      rw [hl]; exact hd
    obtain ⟨b,hb,_⟩ := T.val.property.2.2 v.val.2 d hdt
    have hdu : d < (U.val.val.graph.label (f.toFun v.val.1)).1 := by
      change d < ((presentation U).graph.label (f.toFun v.val.1)).1
      rw [f.label]; exact hd
    have hfa := f.edge v.val.1 d a ha
    have hgb := g.edge v.val.2 d b hb
    have hgb' : U.val.val.graph.edge (f.toFun v.val.1) d (Sum.map g.toFun id b) := by
      change (presentation U).graph.edge (f.toFun v.val.1) d (Sum.map g.toFun id b)
      rw [v.property]
      exact hgb
    have hab := (U.val.property.2.2 (f.toFun v.val.1) d hdu).unique hfa hgb'
    have hex : ∃ z, G.edge v d z := by
      cases a with
      | inl a =>
        cases b with
        | inl b => exact ⟨.inl ⟨(a,b),Sum.inl.inj hab⟩,ha,hb⟩
        | inr j => cases hab
      | inr i =>
        cases b with
        | inl b => cases hab
        | inr j => cases Sum.inr.inj hab; exact ⟨.inr i,ha,hb⟩
    obtain ⟨z,hz⟩ := hex
    refine ⟨z,hz,?_⟩
    intro z' hz'
    exact fiber_target_inj f g z' z
      ((S.val.property.2.2 v.val.1 d hd).unique hz'.1 hz.1)
      ((T.val.property.2.2 v.val.2 d hdt).unique hz'.2 hz.2)

/--
---
conclusion: Lax369799.SupportedMorphisms.system_pullback
---
The reachable part of the fiber product is deterministic. Its projections
lift all outputs from either factor. Pairing any two compatible maps from
a system lands in this reachable part and is the unique factorization.
-/
theorem system_pullback {A : RankedSet} {n : ℕ} (S T U : SupportedSystems.System A n)
    (f : Morphism (presentation S) (presentation U))
    (g : Morphism (presentation T) (presentation U)) :
    ∃ (P : SupportedSystems.System A n) (p : Morphism (presentation P) (presentation S))
      (q : Morphism (presentation P) (presentation T)),
      f.toFun ∘ p.toFun = g.toFun ∘ q.toFun ∧ Folding p ∧ Folding q ∧
      (∀ (V : SupportedSystems.System A n) (a : Morphism (presentation V) (presentation S))
        (b : Morphism (presentation V) (presentation T)),
        f.toFun ∘ a.toFun = g.toFun ∘ b.toFun →
        ∃! h : Morphism (presentation V) (presentation P),
          p.toFun ∘ h.toFun = a.toFun ∧ q.toFun ∘ h.toFun = b.toFun) := by
  classical
  let G := FiniteStructureTheorems.graph f g
  let P : RankedSystems.System A n := ⟨trim G,fiber_deterministic S T U f g⟩
  let p₀ := Pullbacks.project (FiniteStructureTheorems.first f g)
  let q₀ := Pullbacks.project (FiniteStructureTheorems.second f g)
  let p : Morphism (ofSetSystem P.val) (presentation S) :=
    ⟨p₀.toFun,p₀.initial,p₀.root,p₀.label,p₀.edge⟩
  let q : Morphism (ofSetSystem P.val) (presentation T) :=
    ⟨q₀.toFun,q₀.initial,q₀.root,q₀.label,q₀.edge⟩
  let Ps : SupportedSystems.System A n := ⟨P,source_support P S p⟩
  refine ⟨Ps,p,q,?_,deterministic_folding P S.val p,deterministic_folding P T.val q,?_⟩
  · funext v
    exact (Pullbacks.vertex G v).property
  · intro V a b hab
    let h₀ := Pullbacks.lift (S := V.val.val)
      (FiniteStructureTheorems.pair f g (presentation V) a b hab)
    let h : Morphism (presentation V) (presentation Ps) :=
      ⟨h₀.toFun,h₀.initial,h₀.root,h₀.label,h₀.edge⟩
    have hval (v : V.val.val.Vertex) :
        Pullbacks.vertex G (h.toFun v) = ⟨(a.toFun v,b.toFun v),congrFun hab v⟩ := by
      dsimp only [h,h₀,Pullbacks.lift]
      exact Pullbacks.vertex_index G _ _
    refine ⟨h,⟨?_,?_⟩,?_⟩
    · funext v
      exact congrArg (fun w => w.val.1) (hval v)
    · funext v
      exact congrArg (fun w => w.val.2) (hval v)
    · intro h' hprops
      have hp := hprops.1
      have hq := hprops.2
      apply finite_morphism_ext
      funext v
      apply Pullbacks.vertex_injective G
      rw [hval]
      apply Subtype.ext
      exact Prod.ext (congrFun hp v) (congrFun hq v)

end Lax369799Proofs.SupportedMorphisms
