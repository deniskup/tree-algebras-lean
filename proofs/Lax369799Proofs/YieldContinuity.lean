import Lax369799.YieldContinuity
import Lax369799Proofs.ContextResolutionApproximation

set_option backward.isDefEq.respectTransparency false
namespace Lax369799Proofs.YieldContinuity
open Lax369799.RankedSystems Lax369799.Morphisms Lax369799.Flattening
open Lax369799.FiniteResolutionNormalForms Lax369799.YieldContinuity
open Lax369799.PresentationCovers
open Lax369799Proofs.Pullbacks

private def markedGraph {A : RankedSet} {n : ℕ} (D : System A n) (b : Bool) :
    Presentation A n D.val.Vertex := {
  D.val.graph with
  initial := fun v => b = false ∧ v ∈ D.val.graph.initial
  root := fun v => b = true ∧ v ∈ D.val.graph.initial }

def value {A : RankedSet} {n : ℕ} (D : System A n) (b : Bool) : SetSystem A n :=
  if b then plant D.val else D.val

private def markedCover {A : RankedSet} {n : ℕ} {D U : System A n}
    (f : Morphism D.val U.val) (hf : f.LocallySurjective) (b : Bool) :
    Cover (markedGraph D b) (markedGraph U b) where
  toFun := f.toFun
  label := f.label
  initial := fun v h => ⟨h.1, f.initial v h.2⟩
  root := fun v h => ⟨h.1, f.initial v h.2⟩
  edge := f.edge
  initial_lift := by
    rintro w ⟨hb, hw⟩
    obtain ⟨v, hv, he⟩ := hf.1 w hw
    exact ⟨v, ⟨hb, hv⟩, he⟩
  root_lift := by
    rintro w ⟨hb, hw⟩
    obtain ⟨v, hv, he⟩ := hf.1 w hw
    exact ⟨v, ⟨hb, hv⟩, he⟩
  edge_lift := hf.2.2

def valueCover {A : RankedSet} {n : ℕ} (D : System A n) (b : Bool) :
    Cover (markedGraph D b) (value D b).graph := by
  cases b with
  | false =>
    exact {
      toFun := id
      label := fun _ => rfl
      initial := fun _ h => h.2
      root := fun _ h => False.elim (Bool.false_ne_true h.1)
      edge := by intro v d t h; cases t <;> exact h
      initial_lift := fun w h => ⟨w, ⟨rfl, h⟩, rfl⟩
      root_lift := by intro w h; change w ∈ D.val.graph.root at h; rw [D.property.2.1] at h; exact False.elim h
      edge_lift := by intro v d t h; exact ⟨t, h, by cases t <;> rfl⟩ }
  | true =>
    exact {
      toFun := id
      label := fun _ => rfl
      initial := fun _ h => False.elim (Bool.false_ne_true h.1.symm)
      root := fun _ h => Or.inr h.2
      edge := by intro v d t h; cases t <;> exact h
      initial_lift := fun _ h => False.elim h
      root_lift := by
        intro w h
        rcases h with h | h
        · rw [D.property.2.1] at h; exact False.elim h
        · exact ⟨w, ⟨rfl, h⟩, rfl⟩
      edge_lift := by intro v d t h; exact ⟨t, h, by cases t <;> rfl⟩ }

theorem witness {A : RankedSet} {n : ℕ} {S T : SetSystem A n} (h : Yield S T) :
    ∃ c : Component S, Nonempty (Cover (markedGraph c.system c.rooted) T.graph) := by
  rcases h with ⟨U, ⟨D, hd, f, hf⟩, rfl⟩ | ⟨U, ⟨D, hd, f, hf⟩, rfl⟩
  · exact ⟨⟨D, false, hd⟩, ⟨FiniteCovers.compose (markedCover f hf false) (valueCover U false)⟩⟩
  · exact ⟨⟨D, true, hd⟩, ⟨FiniteCovers.compose (markedCover f hf true) (valueCover U true)⟩⟩

private def sumCover {A : RankedSet} {n : ℕ} {I : Type} {S : SetSystem A n}
    (c : I → Component S) (F : I → SetSystem A n)
    (f : ∀ i, Cover (markedGraph (c i).system (c i).rooted) (F i).graph) :
    Cover (familyGraph c) (sumGraph F) where
  toFun := fun v => ⟨v.1, (f v.1).toFun v.2⟩
  label := fun v => (f v.1).label v.2
  initial := fun v h => (f v.1).initial v.2 h
  root := fun v h => (f v.1).root v.2 h
  edge := by
    rintro v d t ⟨s, hs, rfl⟩
    exact ⟨Sum.map (f v.1).toFun id s, (f v.1).edge v.2 d s hs, by cases s <;> rfl⟩
  initial_lift := by
    rintro ⟨i, w⟩ hw
    obtain ⟨v, hv, he⟩ := (f i).initial_lift w hw
    exact ⟨⟨i, v⟩, hv, by cases he; rfl⟩
  root_lift := by
    rintro ⟨i, w⟩ hw
    obtain ⟨v, hv, he⟩ := (f i).root_lift w hw
    exact ⟨⟨i, v⟩, hv, by cases he; rfl⟩
  edge_lift := by
    rintro v d t ⟨s, hs, rfl⟩
    obtain ⟨u, hu, he⟩ := (f v.1).edge_lift v.2 d s hs
    refine ⟨Sum.map (Sigma.mk v.1) id u, ⟨u, hu, rfl⟩, ?_⟩
    rw [← he]
    cases u <;> rfl

theorem family_equivalent {A : RankedSet} {n : ℕ} {I : Type} [Fintype I]
    {S : SetSystem A n} (c : I → Component S) (F : I → SetSystem A n)
    (f : ∀ i, Cover (markedGraph (c i).system (c i).rooted) (F i).graph) :
    YieldEquivalent (trim (family c).graph) (finiteSum F) := by
  classical
  let a := FiniteCovers.isoCover (UntrimmedFlattening.isoSymm
    (UntrimmedFlattening.reindexIso (familyGraph c) (Fintype.equivFin _)))
  let g := FiniteCovers.compose a (sumCover c F f)
  let gm : Map (family c).graph (sumGraph F) := ⟨g.toFun, g.initial, g.root, g.label, g.edge⟩
  exact (Yields.morphism_yields (trimMap gm)).2
    (trimMap_surjective gm g.initial_lift g.root_lift g.edge_lift)

theorem component_yield {A : RankedSet} {n : ℕ} {S : SetSystem A n} (c : Component S) :
    Yield S (value c.system c.rooted) := by
  have h := c.resolves
  cases hb : c.rooted with
  | false =>
    simp only [hb, Bool.false_eq_true, ↓reduceIte] at h
    exact Or.inl ⟨c.system, ⟨c.system, h, MorphismTheorems.identity _, MorphismTheorems.identity_surjective _⟩, rfl⟩
  | true =>
    simp only [hb, ↓reduceIte] at h
    exact Or.inr ⟨c.system, ⟨c.system, h, MorphismTheorems.identity _, MorphismTheorems.identity_surjective _⟩, rfl⟩

/--
---
conclusion: Lax369799.YieldContinuity.continuity
---
Finite context approximation supplies a family of initial and planted
root resolutions. For the converse, choose an unfolding witness for
each proposed yield. Their disjoint family covers the proposed sum and
maps into the original system; yield congruence transfers both maps
through the context.
-/
theorem continuity {A : RankedSet} {k n : ℕ}
    (C : SetContext A k n) (S : SetSystem A k) (R : SetSystem A n) :
    Yield (plug C S) R ↔
      ∃ (m : ℕ) (F : Fin m → SetSystem A k),
        (∀ i, Yield S (F i)) ∧ Yield (plug C (finiteSum F)) R := by
  classical
  constructor
  · intro hr
    obtain ⟨m, c, hc⟩ := (ContextResolutionApproximation.yields C S R).mp hr
    let F := fun i => value (c i).system (c i).rooted
    have he := family_equivalent c F (fun i => valueCover (c i).system (c i).rooted)
    refine ⟨m, F, fun i => component_yield (c i), ?_⟩
    exact YieldObservations.yield_context_congruence C _ _ (fun U h => (he U).mp h) R hc
  · rintro ⟨m, F, hF, hr⟩
    let c := fun i => Classical.choose (witness (hF i))
    let f := fun i => Classical.choice (Classical.choose_spec (witness (hF i)))
    have he := family_equivalent c F f
    have hr := YieldObservations.yield_context_congruence C _ _ (fun U h => (he U).mpr h) R hr
    exact (ContextResolutionApproximation.yields C S R).mpr ⟨m, c, hr⟩

end Lax369799Proofs.YieldContinuity
