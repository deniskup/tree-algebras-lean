import Lax369799.SupportedResolutions
import Lax369799Proofs.SupportedYieldComparison
import Lax369799Proofs.SupportedSystems
import Lax369799Proofs.SystemSubstitution

set_option backward.isDefEq.respectTransparency false
namespace Lax369799Proofs.SupportedResolutions
open Lax369799
open RankedSystems FinitePresentations SupportedMorphisms FiniteRenaming SupportedYields
open Lax369799.SupportedResolutions

private def pushRaw {A : RankedSet} {m n : ℕ} {V : Type} (σ : Fin m → Fin n)
    (G : Presentation A m V) : Presentation A n V where
  label := G.label
  initial := G.initial
  root := G.root
  edge := fun v d t => ∃ s,G.edge v d s ∧ t = Sum.map id σ s
  direction_valid := by rintro v d t ⟨s,hs,_⟩; exact G.direction_valid v d s hs

private noncomputable def toEnumeration {A : RankedSet} {m n : ℕ} {V W : Type}
    [Fintype V] [Fintype W] (G : Presentation A m V) (H : Presentation A n W) (τ : Fin m → Fin n)
    (f : Pullbacks.Map (pushRaw τ G) H) :
    FiniteMorphisms.Morphism (push τ (ofSetSystem (trim G))) (enumerate H) :=
  FiniteMorphisms.toEnumeration {
    toFun := fun v => f.toFun (Pullbacks.vertex G v)
    label := fun v => f.label (Pullbacks.vertex G v)
    initial := fun v h => f.initial _ h
    root := fun v h => f.root _ h
    edge := by
      rintro v d t ⟨s,hs,rfl⟩
      have hf := f.edge (Pullbacks.vertex G v) d (Sum.map (Pullbacks.vertex G) τ s)
        ⟨Sum.map (Pullbacks.vertex G) id s,hs,by cases s <;> rfl⟩
      cases s <;> exact hf }

private theorem unfold_equivalent {A : RankedSet} {n : ℕ} (S T : SupportedSystems.System A n)
    (h : Morphisms.UnfoldEquivalent S.val.val T.val.val) :
    FiniteStructureTheorems.UnfoldEquivalent (presentation S) (presentation T) := by
  obtain ⟨P,⟨p,hp⟩,⟨q,_⟩⟩ := h
  obtain ⟨W,⟨w⟩,⟨f,_⟩⟩ := Yields.lift_resolution p hp S.val (MorphismTheorems.identity _)
  let f' : FiniteMorphisms.Morphism (ofSetSystem W.val) (presentation S) :=
    ⟨f.toFun,f.initial,f.root,f.label,f.edge⟩
  let W' : SupportedSystems.System A n := ⟨W,SupportedMorphisms.source_support W S f'⟩
  let g := MorphismTheorems.compose w q
  let g' : FiniteMorphisms.Morphism (presentation W') (presentation T) :=
    ⟨g.toFun,g.initial,g.root,g.label,g.edge⟩
  exact ⟨presentation W',f',g',SupportedMorphisms.system_folding W' S f',SupportedMorphisms.system_folding W' T g'⟩

private def identity {A : RankedSet} {n : ℕ} (S : FiniteSystem A n) : FiniteMorphisms.Morphism S S where
  toFun := id
  label := fun _ => rfl
  initial := fun _ h => h
  root := fun _ h => h
  edge := by intro v d t h; cases t <;> exact h

/--
---
conclusion: Lax369799.SupportedResolutions.sound
---
Choose supported direct witnesses for the local yields and flatten them.
Pair the outer and inner vertex maps to obtain the renamed resolution.
Pointwise unfolding invariance transfers its target to the original
supported flattening (Lemma 46).
-/
theorem sound {A : RankedSet} {m n : ℕ} (S : FiniteSystem (FiniteSystem A) n)
    (T : SupportedSystems.System (SupportedSystems.System A) m) (τ : Fin m → Fin n)
    (r : Resolution S T τ) (V : SupportedSystems.System A m)
    (hV : Flattening.SystemFlattening (SupportedSystems.forgetPattern T) V.val) :
    InitialYield (flatten S) V τ := by
  classical
  choose U a b hb using r.resolves
  let T' : SupportedSystems.System (SupportedSystems.System A) m :=
    ⟨⟨ProfileSubstitution.withLabels T.val.val U,T.val.property⟩,T.property⟩
  obtain ⟨W,hW⟩ := SupportedSystems.flatten_system T'
  let G := flattenPresentation (SupportedSystems.pattern T').graph
  let H := flattenPresentation S.graph
  let f : Pullbacks.Map (pushRaw τ G) H := {
    toFun := fun v => ⟨r.vertex v.1,(a v.1).toFun v.2⟩
    label := fun v => (a v.1).label v.2
    initial := fun v h => ⟨r.initial v.1 h.1,(a v.1).initial v.2 h.2⟩
    root := by
      intro v h
      rcases h with h | ⟨h,_⟩
      · have hh := (U v.1).val.property.2.1
        change (U v.1).val.val.graph.root v.2 at h
        rw [hh] at h; exact h.elim
      · change T.val.val.graph.root v.1 at h
        rw [T.val.property.2.1] at h; exact h.elim
    edge := by
      rintro v d t ⟨s,hs,rfl⟩
      rcases hs with ⟨w,hw,rfl⟩ | ⟨i,hi,hs⟩
      · have ha := (a v.1).edge v.2 d (.inl w) ⟨.inl w,hw,rfl⟩
        exact Or.inl ⟨(a v.1).toFun w,ha,rfl⟩
      · have ha := (a v.1).edge v.2 d (.inr (r.variableMap v.1 i)) ⟨.inr i,hi,rfl⟩
        refine Or.inr ⟨r.variableMap v.1 i,ha,?_⟩
        rcases hs with ⟨w,hw,hi',rfl⟩ | ⟨j,hj,rfl⟩
        · exact Or.inl ⟨⟨r.vertex w.1,(a w.1).toFun w.2⟩,
            r.transition v.1 i w.1 hw,(a w.1).initial w.2 hi',rfl⟩
        · exact Or.inr ⟨τ j,r.exit v.1 i j hj,rfl⟩ }
  have hW' : W.val.val = trim G := hW
  have direct : Nonempty (FiniteMorphisms.Morphism (push τ (presentation W)) (flatten S)) := by
    change Nonempty (FiniteMorphisms.Morphism (push τ (ofSetSystem W.val.val)) (enumerate H))
    rw [hW']
    exact ⟨toEnumeration G H τ f⟩
  have hy : InitialYield (flatten S) W τ :=
    ⟨W,direct.some,identity (presentation W),SupportedMorphisms.system_folding W W (identity (presentation W))⟩
  have pointwise (v : T.val.val.Vertex) : Morphisms.UnfoldEquivalent (U v).val.val (T.val.val.graph.label v).2.val.val := by
    let g : Morphisms.Morphism (U v).val.val (T.val.val.graph.label v).2.val.val :=
      ⟨(b v).toFun,(b v).initial,(b v).root,(b v).label,(b v).edge⟩
    exact ⟨(U v).val.val,⟨MorphismTheorems.identity _,MorphismTheorems.identity_surjective _⟩,g,(hb v).1⟩
  have he := SystemSubstitution.pointwise_unfold T.val
    (fun v => (U v).val) (fun v => (T.val.val.graph.label v).2.val) pointwise W.val V.val hW hV
  exact (SupportedYields.unfold_invariance (flatten S) W V τ (unfold_equivalent W V he)).1.mp hy

end Lax369799Proofs.SupportedResolutions
