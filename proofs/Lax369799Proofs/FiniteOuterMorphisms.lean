import Lax369799Proofs.FiniteCovers
import Lax369799.FiniteOrderedAlgebra

namespace Lax369799Proofs.FiniteOuterMorphisms
open Lax369799.RankedSystems (RankedSet Symbol)
open Lax369799.FinitePresentations Lax369799.FiniteMorphisms
open Lax369799Proofs.Pullbacks

private def castVertex {A : RankedSet} {a b : Symbol (FiniteSystem A)} (h : a = b)
    (v : a.2.Vertex) : b.2.Vertex := h ▸ v

private theorem cast_label {A : RankedSet} {a b : Symbol (FiniteSystem A)} (h : a = b)
    (v : a.2.Vertex) : b.2.graph.label (castVertex h v) = a.2.graph.label v := by
  cases h
  rfl

private theorem cast_initial {A : RankedSet} {a b : Symbol (FiniteSystem A)} (h : a = b)
    {v : a.2.Vertex} (hv : a.2.graph.initial v) : b.2.graph.initial (castVertex h v) := by
  cases h
  exact hv

private theorem cast_root {A : RankedSet} {a b : Symbol (FiniteSystem A)} (h : a = b)
    {v : a.2.Vertex} (hv : a.2.graph.root v) : b.2.graph.root (castVertex h v) := by
  cases h
  exact hv

private theorem cast_edge {A : RankedSet} {a b : Symbol (FiniteSystem A)} (h : a = b)
    {v : a.2.Vertex} {d : ℕ} {t : a.2.Vertex ⊕ Fin a.1} (ht : a.2.graph.edge v d t) :
    b.2.graph.edge (castVertex h v) d
      (Sum.map (castVertex h) (Fin.cast (congrArg Sigma.fst h)) t) := by
  cases h
  cases t <;> exact ht

private def flattenMap {A : RankedSet} {n : ℕ} {V W : Type}
    {S : Lax369799.RankedSystems.Presentation (FiniteSystem A) n V}
    {T : Lax369799.RankedSystems.Presentation (FiniteSystem A) n W}
    (f : Map S T) : Map (flattenPresentation S) (flattenPresentation T) where
  toFun := fun v => ⟨f.toFun v.1, castVertex (f.label v.1).symm v.2⟩
  label := fun v => cast_label (f.label v.1).symm v.2
  initial := fun v h => ⟨f.initial v.1 h.1, cast_initial (f.label v.1).symm h.2⟩
  root := fun v h => h.elim (fun h => Or.inl (cast_root (f.label v.1).symm h))
    (fun h => Or.inr ⟨f.root v.1 h.1, cast_initial (f.label v.1).symm h.2⟩)
  edge := by
    intro v d t ht
    rcases ht with ⟨w, hw, rfl⟩ | ⟨i, hi, ht⟩
    · exact Or.inl ⟨castVertex (f.label v.1).symm w, cast_edge (f.label v.1).symm hw, rfl⟩
    · let j := Fin.cast (congrArg Sigma.fst (f.label v.1).symm) i
      refine Or.inr ⟨j, cast_edge (f.label v.1).symm hi, ?_⟩
      rcases ht with ⟨w, hw, hi', rfl⟩ | ⟨k, hk, rfl⟩
      · exact Or.inl ⟨⟨f.toFun w.1, castVertex (f.label w.1).symm w.2⟩,
          f.edge v.1 i.val (.inl w.1) hw, cast_initial (f.label w.1).symm hi', rfl⟩
      · exact Or.inr ⟨k, f.edge v.1 i.val (.inr k) hk, rfl⟩

private theorem cast_roundtrip {A : RankedSet} {a b : Symbol (FiniteSystem A)} (h : a = b)
    (v : a.2.Vertex) : castVertex h.symm (castVertex h v) = v := by
  cases h
  rfl

private def flattenCoverSupported {A : RankedSet} {n : ℕ} {V W : Type}
    {S : Lax369799.RankedSystems.Presentation (FiniteSystem A) n V}
    {T : Lax369799.RankedSystems.Presentation (FiniteSystem A) n W}
    (f : Lax369799.PresentationCovers.Cover S T)
    (hf : ∀ w (u : (Inner T w).Vertex), (Inner T w).graph.root u → ∃ v, f.toFun v = w) :
    Lax369799.PresentationCovers.Cover (flattenPresentation S) (flattenPresentation T) := by
  let m : Map S T := ⟨f.toFun, f.initial, f.root, f.label, f.edge⟩
  let g := flattenMap m
  refine {
    toFun := g.toFun
    label := g.label
    initial := g.initial
    root := g.root
    edge := g.edge
    initial_lift := ?_
    root_lift := ?_
    edge_lift := ?_ }
  · rintro ⟨w, u⟩ ⟨hw, hu⟩
    obtain ⟨v, hv, rfl⟩ := f.initial_lift w hw
    refine ⟨⟨v, castVertex (f.label v) u⟩, ⟨hv, cast_initial (f.label v) hu⟩, ?_⟩
    exact congrArg (Sigma.mk (f.toFun v)) (cast_roundtrip (f.label v) u)
  · rintro ⟨w, u⟩ (hu | ⟨hw, hu⟩)
    · obtain ⟨v, rfl⟩ := hf w u hu
      refine ⟨⟨v, castVertex (f.label v) u⟩, Or.inl (cast_root (f.label v) hu), ?_⟩
      exact congrArg (Sigma.mk (f.toFun v)) (cast_roundtrip (f.label v) u)
    · obtain ⟨v, hv, rfl⟩ := f.root_lift w hw
      refine ⟨⟨v, castVertex (f.label v) u⟩, Or.inr ⟨hv, cast_initial (f.label v) hu⟩, ?_⟩
      exact congrArg (Sigma.mk (f.toFun v)) (cast_roundtrip (f.label v) u)
  · intro v d t ht
    have back {s} (hs : (Inner T (f.toFun v.1)).graph.edge
        (castVertex (f.label v.1).symm v.2) d s) :
        (Inner S v.1).graph.edge v.2 d
          (Sum.map (castVertex (f.label v.1)) (Fin.cast (congrArg Sigma.fst (f.label v.1))) s) := by
      have hh := cast_edge (f.label v.1) hs
      simpa only [cast_roundtrip] using hh
    rcases ht with ⟨w, hw, rfl⟩ | ⟨i, hi, ht⟩
    · refine ⟨.inl ⟨v.1, castVertex (f.label v.1) w⟩,
        Or.inl ⟨castVertex (f.label v.1) w, back hw, rfl⟩, ?_⟩
      exact congrArg (fun x => Sum.inl (Sigma.mk (f.toFun v.1) x)) (cast_roundtrip (f.label v.1) w)
    · let j := Fin.cast (congrArg Sigma.fst (f.label v.1)) i
      rcases ht with ⟨⟨w, u⟩, hw, hu, rfl⟩ | ⟨k, hk, rfl⟩
      · obtain ⟨s, hs, he⟩ := f.edge_lift v.1 i.val (.inl w) hw
        cases s with
        | inr k => cases he
        | inl x =>
          cases Sum.inl.inj he
          refine ⟨.inl ⟨x, castVertex (f.label x) u⟩,
            Or.inr ⟨j, back hi, Or.inl ⟨⟨x, castVertex (f.label x) u⟩,
              hs, cast_initial (f.label x) hu, rfl⟩⟩, ?_⟩
          exact congrArg (fun z => Sum.inl (Sigma.mk (f.toFun x) z)) (cast_roundtrip (f.label x) u)
      · obtain ⟨s, hs, he⟩ := f.edge_lift v.1 i.val (.inr k) hk
        cases s with
        | inl x => cases he
        | inr l =>
          cases Sum.inr.inj he
          exact ⟨.inr l, Or.inr ⟨j, back hi, Or.inr ⟨l, hs, rfl⟩⟩, rfl⟩

noncomputable def flattenCover {A : RankedSet} {n : ℕ} {S T : FiniteSystem (FiniteSystem A) n}
    (f : Lax369799.PresentationCovers.Cover S.graph T.graph) (hf : Function.Surjective f.toFun) :
    Lax369799.PresentationCovers.Cover (flatten S).graph (flatten T).graph :=
  FiniteCovers.enumerateCover (flattenCoverSupported f (fun w _ _ => hf w))

def flattenCoverRootlessRaw {A : RankedSet} {n : ℕ} {V W : Type}
    {S : Lax369799.RankedSystems.Presentation (FiniteSystem A) n V}
    {T : Lax369799.RankedSystems.Presentation (FiniteSystem A) n W}
    (f : Lax369799.PresentationCovers.Cover S T)
    (h : ∀ w, (Inner T w).graph.root = ∅) :
    Lax369799.PresentationCovers.Cover (flattenPresentation S) (flattenPresentation T) :=
  flattenCoverSupported f (by
    intro w u hu
    rw [h w] at hu
    exact False.elim hu)

noncomputable def flattenCoverRootless {A : RankedSet} {n : ℕ}
    {S T : FiniteSystem (FiniteSystem A) n}
    (f : Lax369799.PresentationCovers.Cover S.graph T.graph)
    (h : ∀ w, (Inner T.graph w).graph.root = ∅) :
    Lax369799.PresentationCovers.Cover (flatten S).graph (flatten T).graph :=
  FiniteCovers.enumerateCover (flattenCoverSupported f (by
    intro w u hu
    rw [h w] at hu
    exact False.elim hu))

noncomputable def flattenMorphism {A : RankedSet} {n : ℕ} {S T : FiniteSystem (FiniteSystem A) n}
    (f : Morphism S T) : Morphism (flatten S) (flatten T) :=
  FiniteMorphisms.enumerateMap (flattenMap (FiniteMorphisms.asMap f))

def relabelMorphism {A B : RankedSet} (g : Lax369799.RankedSystems.RankedMap A B)
    {n : ℕ} {S T : FiniteSystem A n} (f : Morphism S T) : Morphism (relabel g S) (relabel g T) where
  toFun := f.toFun
  initial := f.initial
  root := f.root
  label := fun v => congrArg (fun a : Symbol A => (⟨a.1, g a.1 a.2⟩ : Symbol B)) (f.label v)
  edge := f.edge

open Lax369799.FiniteContextualOrder Lax369799.FiniteAcceptance Lax369799.FiniteSyntacticAlgebra

/--
---
conclusion: Lax369799.FiniteOrderedAlgebra.evaluation_morphism
---
Relabel an outer morphism by presentation representatives and lift it
through flattening, retaining every inner root. The resulting morphism
reverses the contextual order on the evaluated classes.
-/
theorem evaluation_morphism {A : RankedSet} (L : Lax369799.Algebras.Language A)
    (E : Algebra (Carrier (Accepting L)))
    (hE : ∀ n (S : FiniteSystem (FiniteSystem A) n),
      E.eval n (relabel (quotientMap (Accepting L)) S) = quotientMap (Accepting L) n (flatten S))
    {n : ℕ} {S T : FiniteSystem (Carrier (Accepting L)) n} (f : Morphism S T) :
    ClassBelow (Accepting L) (E.eval n T) (E.eval n S) := by
  rw [FiniteSyntacticAlgebra.evaluation_by_representatives (Accepting L) E hE T,
    FiniteSyntacticAlgebra.evaluation_by_representatives (Accepting L) E hE S]
  exact FiniteMorphisms.contextual_morphism L (flattenMorphism (relabelMorphism (fun _ a => a.out) f))

def relabelCover {A B : RankedSet} (g : Lax369799.RankedSystems.RankedMap A B)
    {n : ℕ} {S T : FiniteSystem A n} (f : Lax369799.PresentationCovers.Cover S.graph T.graph) :
    Lax369799.PresentationCovers.Cover (relabel g S).graph (relabel g T).graph where
  toFun := f.toFun
  label := fun v => congrArg (fun a : Symbol A => (⟨a.1, g a.1 a.2⟩ : Symbol B)) (f.label v)
  initial := f.initial
  root := f.root
  edge := f.edge
  initial_lift := f.initial_lift
  root_lift := f.root_lift
  edge_lift := f.edge_lift

/--
---
conclusion: Lax369799.FiniteOrderedAlgebra.evaluation_cover
---
A cover that reaches every outer vertex lifts through substitution.
Global surjectivity supplies preimages for roots inside labels even when
the corresponding outer vertex is unreachable. Contextual invariance of
the resulting cover identifies the two evaluation classes.
-/
theorem evaluation_cover {A : RankedSet} (L : Lax369799.Algebras.Language A)
    (E : Algebra (Carrier (Accepting L)))
    (hE : ∀ n (S : FiniteSystem (FiniteSystem A) n),
      E.eval n (relabel (quotientMap (Accepting L)) S) = quotientMap (Accepting L) n (flatten S))
    {n : ℕ} {S T : FiniteSystem (Carrier (Accepting L)) n}
    (f : Lax369799.PresentationCovers.Cover S.graph T.graph) (hf : Function.Surjective f.toFun) :
    E.eval n S = E.eval n T := by
  rw [FiniteSyntacticAlgebra.evaluation_by_representatives (Accepting L) E hE S,
    FiniteSyntacticAlgebra.evaluation_by_representatives (Accepting L) E hE T]
  exact Quot.sound (FiniteCovers.contextual_cover L
    (flattenCover (relabelCover (fun _ a => a.out) f) hf))

end Lax369799Proofs.FiniteOuterMorphisms
