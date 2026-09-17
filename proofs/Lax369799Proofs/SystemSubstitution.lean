import Lax369799.SystemSubstitution
import Lax369799Proofs.FiniteOuterMorphisms
import Lax369799Proofs.Flattening

set_option backward.isDefEq.respectTransparency false
namespace Lax369799Proofs.SystemSubstitution
open Lax369799.RankedSystems Lax369799.Morphisms Lax369799.Flattening
open Lax369799.PolynomialContexts Lax369799.PresentationCovers
open Lax369799Proofs.Pullbacks

private def asCover {A : RankedSet} {n : ℕ} {S T : SetSystem A n}
    (f : Morphism S T) (hf : f.LocallySurjective) : Cover S.graph T.graph :=
  ⟨f.toFun, f.label, f.initial, f.root, f.edge, hf.1, hf.2.1, hf.2.2⟩

private theorem trim_cover {A : RankedSet} {n : ℕ} {V W : Type} [Fintype V] [Fintype W]
    {G : Presentation A n V} {H : Presentation A n W} (f : Cover G H) : UnfoldsTo (trim H) (trim G) := by
  let g : Map G H := ⟨f.toFun, f.initial, f.root, f.label, f.edge⟩
  exact ⟨trimMap g, trimMap_surjective g f.initial_lift f.root_lift f.edge_lift⟩

/--
---
conclusion: Lax369799.SystemSubstitution.pointwise_unfold
---
Choose a common cover for each pair of inner systems, substitute these
covers into the fixed outer pattern, and restrict the resulting covers to
reachable vertices.
-/
theorem pointwise_unfold {A C : RankedSet} {n : ℕ} (P : System C n)
    (q r : ∀ v, System A (P.val.graph.label v).1)
    (h : ∀ v, UnfoldEquivalent (q v).val (r v).val)
    (U V : System A n) (hU : SystemFlattening (withLabels P q) U)
    (hV : SystemFlattening (withLabels P r) V) : UnfoldEquivalent U.val V.val := by
  classical
  let W := fun v => Classical.choose (h v)
  let f := fun v => Classical.choose (Classical.choose_spec (h v)).1
  have hf := fun v => Classical.choose_spec (Classical.choose_spec (h v)).1
  let g := fun v => Classical.choose (Classical.choose_spec (h v)).2
  have hg := fun v => Classical.choose_spec (Classical.choose_spec (h v)).2
  let left := FiniteCovers.substituteCover P.val.graph
    (fun v => (W v).graph) (fun v => (q v).val.graph) (fun v => asCover (f v) (hf v))
  let right := FiniteCovers.substituteCover P.val.graph
    (fun v => (W v).graph) (fun v => (r v).val.graph) (fun v => asCover (g v) (hg v))
  rw [hU, hV]
  exact ⟨_, trim_cover left, trim_cover right⟩

/--
---
conclusion: Lax369799.SystemSubstitution.outer_morphism
---
A morphism between systems is locally surjective. Relabel by the underlying
finite inner presentations and lift the outer cover through substitution.
Inner systems have no roots, which supplies the required root-free condition.
-/
theorem outer_morphism {A : RankedSet} {n : ℕ} (S T : System (System A) n)
    (f : Morphism S.val T.val) (U V : System A n)
    (hU : SystemFlattening S U) (hV : SystemFlattening T V) : UnfoldsTo V.val U.val := by
  let c := asCover f (MorphismTheorems.system_morphism_locally_surjective S T f)
  let g := FiniteOuterMorphisms.relabelCover
    (fun _ (R : System A _) => Lax369799.FinitePresentations.ofSetSystem R.val)
    (S := Lax369799.FinitePresentations.ofSetSystem S.val)
    (T := Lax369799.FinitePresentations.ofSetSystem T.val) c
  let d := FiniteOuterMorphisms.flattenCoverRootlessRaw g
    (fun v => (T.val.graph.label v).2.property.2.1)
  rw [hU, hV]
  exact trim_cover d

/--
---
conclusion: Lax369799.SystemSubstitution.evaluation
---
Relabel the flattened system and its inner components by the same alphabet
map. Relabelling commutes with flattening, so algebra associativity applies.
-/
theorem evaluation {A B C : RankedSet} (E : Lax369799.Algebras.Algebra B) (η : RankedMap A B)
    (f : RankedMap C (System A)) {n : ℕ} (S : System C n) (U : System A n)
    (hU : SystemFlattening (relabelSystem f S) U) :
    E.eval n (relabelSystem η U) = E.eval n
      (relabelSystem (fun k a => E.eval k (relabelSystem η (f k a))) S) := by
  let T := relabelSystem (fun k a => relabelSystem η (f k a)) S
  have ht : SystemFlattening T (relabelSystem η U) := by
    change relabel η U.val = _
    rw [hU]
    rfl
  exact (E.associative n T (relabelSystem η U) ht).symm

theorem common_system {A : RankedSet} {n : ℕ} (S T : System A n)
    (h : UnfoldEquivalent S.val T.val) :
    ∃ R : System A n, Nonempty (Morphism R.val S.val) ∧ Nonempty (Morphism R.val T.val) := by
  obtain ⟨W, ⟨f, hf⟩, ⟨g, _⟩⟩ := h
  obtain ⟨R, ⟨r⟩, _⟩ := Yields.lift_resolution f hf S (MorphismTheorems.identity S.val)
  exact ⟨R, ⟨MorphismTheorems.compose r f⟩, ⟨MorphismTheorems.compose r g⟩⟩

def relabelMorphism {A B : RankedSet} (η : RankedMap A B) {n : ℕ}
    {S T : SetSystem A n} (f : Morphism S T) : Morphism (relabel η S) (relabel η T) where
  toFun := f.toFun
  initial := f.initial
  root := f.root
  label := fun v => congrArg (fun a : Symbol A => (⟨a.1, η a.1 a.2⟩ : Symbol B)) (f.label v)
  edge := f.edge

theorem relabel_unfold {A B : RankedSet} (η : RankedMap A B) {n : ℕ}
    {S T : SetSystem A n} (h : UnfoldEquivalent S T) : UnfoldEquivalent (relabel η S) (relabel η T) := by
  obtain ⟨R, ⟨f, hf⟩, ⟨g, hg⟩⟩ := h
  exact ⟨relabel η R, ⟨relabelMorphism η f, hf⟩, ⟨relabelMorphism η g, hg⟩⟩

theorem outer_unfold {A : RankedSet} {n : ℕ} (S T : System (System A) n)
    (h : UnfoldEquivalent S.val T.val) (U V : System A n)
    (hU : SystemFlattening S U) (hV : SystemFlattening T V) : UnfoldEquivalent U.val V.val := by
  obtain ⟨R, ⟨f⟩, ⟨g⟩⟩ := common_system S T h
  obtain ⟨W, hw⟩ := Flattening.flatten_system R
  exact ⟨W.val, outer_morphism R S f W U hw hU, outer_morphism R T g W V hw hV⟩

end Lax369799Proofs.SystemSubstitution
