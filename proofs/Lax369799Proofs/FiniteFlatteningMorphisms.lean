import Lax369799.FiniteFlatteningMorphisms
import Lax369799Proofs.FiniteOuterMorphisms
import Lax369799Proofs.FiniteStructureTheorems

set_option backward.isDefEq.respectTransparency false
namespace Lax369799Proofs.FiniteFlatteningMorphisms
open Lax369799
open RankedSystems (RankedSet Presentation)
open FinitePresentations FiniteMorphisms FiniteStructureTheorems
open Lax369799Proofs.Pullbacks (Map)

private def asCover {A : RankedSet} {n : ℕ} {S T : FiniteSystem A n}
    (f : Morphism S T) (h : LocallySurjective f) : PresentationCovers.Cover S.graph T.graph :=
  ⟨f.toFun,f.label,f.initial,f.root,f.edge,h.1,h.2.1,h.2.2⟩

private theorem enum_surjective {A : RankedSet} {n : ℕ} {V W : Type} [Fintype V] [Fintype W]
    {G : Presentation A n V} {H : Presentation A n W} (f : Map G H)
    (hf : Function.Surjective f.toFun) :
    Function.Surjective (FiniteMorphisms.enumerateMap f).toFun := by
  intro w
  obtain ⟨v,hv⟩ := hf ((Fintype.equivFin W).symm w)
  exact ⟨Fintype.equivFin V v, by simpa [FiniteMorphisms.enumerateMap,
    FiniteMorphisms.toEnumeration] using congrArg (Fintype.equivFin W) hv⟩

/--
---
conclusion: Lax369799.FiniteFlatteningMorphisms.inner
---
Pair the outer vertex with its inner image. Initial, root, and edge lifts
are componentwise; surjectivity on inner vertices covers every pair.
-/
theorem inner {A : RankedSet} {n : ℕ} (P : FiniteSystem (FiniteSystem A) n)
    (Q : ∀ v, FiniteSystem A (P.graph.label v).1)
    (f : ∀ v, Morphism (Inner P.graph v) (Q v)) :
    ∃ g : Morphism (flatten P) (flatten (withLabels P Q)),
      ((∀ v, LocallySurjective (f v)) → LocallySurjective g) ∧
      ((∀ v, Folding (f v)) → Folding g) := by
  classical
  let m := UntrimmedFlattening.substituteMap P.graph
    (fun v => (Inner P.graph v).graph) (fun v => (Q v).graph)
    (fun v => FiniteMorphisms.asMap (f v))
  let g := FiniteMorphisms.enumerateMap m
  have hlocal (hf : ∀ v, LocallySurjective (f v)) : LocallySurjective g := by
    let c := FiniteCovers.enumerateCover (FiniteCovers.substituteCover P.graph
      (fun v => (Inner P.graph v).graph) (fun v => (Q v).graph)
      (fun v => asCover (f v) (hf v)))
    exact ⟨c.initial_lift,c.root_lift,c.edge_lift⟩
  refine ⟨g,hlocal,?_⟩
  intro hf
  refine ⟨hlocal (fun v => (hf v).1),enum_surjective m ?_⟩
  rintro ⟨v,w⟩
  obtain ⟨u,hu⟩ := (hf v).2 w
  exact ⟨⟨v,u⟩,congrArg (Sigma.mk v) hu⟩

private theorem outer_raw_surjective {A : RankedSet} {n : ℕ} {V W : Type}
    {G : Presentation (FiniteSystem A) n V} {H : Presentation (FiniteSystem A) n W}
    (f : Map G H) (hf : Function.Surjective f.toFun) :
    Function.Surjective (FiniteOuterMorphisms.flattenMap f).toFun := by
  rintro ⟨w,u⟩
  obtain ⟨v,rfl⟩ := hf w
  exact ⟨⟨v,FiniteOuterMorphisms.castVertex (f.label v) u⟩,
    congrArg (Sigma.mk (f.toFun v)) (FiniteOuterMorphisms.cast_roundtrip (f.label v) u)⟩

/--
---
conclusion: Lax369799.FiniteFlatteningMorphisms.outer
---
Lift the outer vertex map while transporting the inner vertex along
label equality. Global surjectivity also covers inner roots attached to
unreachable outer vertices.
-/
theorem outer {A : RankedSet} {n : ℕ} {S T : FiniteSystem (FiniteSystem A) n}
    (f : Morphism S T) :
    ∃ g : Morphism (flatten S) (flatten T), Folding f → Folding g := by
  let g := FiniteOuterMorphisms.flattenMorphism f
  refine ⟨g,?_⟩
  intro hf
  let c := FiniteOuterMorphisms.flattenCover (asCover f hf.1) hf.2
  exact ⟨⟨c.initial_lift,c.root_lift,c.edge_lift⟩,
    enum_surjective _ (outer_raw_surjective (FiniteMorphisms.asMap f) hf.2)⟩

/--
---
conclusion: Lax369799.FiniteFlatteningMorphisms.outer_congruence
---
Flatten both foldings from the common unfolding.
-/
theorem outer_congruence {A : RankedSet} {n : ℕ} (S T : FiniteSystem (FiniteSystem A) n)
    (h : UnfoldEquivalent S T) : UnfoldEquivalent (flatten S) (flatten T) := by
  obtain ⟨U,f,g,hf,hg⟩ := h
  obtain ⟨f',hf'⟩ := outer f
  obtain ⟨g',hg'⟩ := outer g
  exact ⟨flatten U,f',g',hf' hf,hg' hg⟩

/--
---
conclusion: Lax369799.FiniteFlatteningMorphisms.inner_congruence
---
Choose common unfoldings at every label of the finite outer shape.
Their componentwise foldings lift to foldings of the flattenings.
-/
theorem inner_congruence {A : RankedSet} {n : ℕ} (P : FiniteSystem (FiniteSystem A) n)
    (Q : ∀ v, FiniteSystem A (P.graph.label v).1)
    (h : ∀ v, UnfoldEquivalent (Inner P.graph v) (Q v)) :
    UnfoldEquivalent (flatten P) (flatten (withLabels P Q)) := by
  classical
  choose U f g hf hg using h
  let R := withLabels P U
  obtain ⟨f',_,hf'⟩ := inner R (fun v => Inner P.graph v) f
  obtain ⟨g',_,hg'⟩ := inner R Q g
  have he : withLabels R (fun v => Inner P.graph v) = P := by
    cases P; rfl
  have result : UnfoldEquivalent (flatten (withLabels R (fun v => Inner P.graph v)))
      (flatten (withLabels R Q)) := ⟨flatten R,f',g',hf' hf,hg' hg⟩
  rw [he] at result
  exact result

end Lax369799Proofs.FiniteFlatteningMorphisms
