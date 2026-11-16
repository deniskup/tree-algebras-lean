import Lax369799.FiniteCoverFamilies
import Lax369799Proofs.ExpandedSyntacticAlgebra
import Lax369799Proofs.FiniteOuterMorphisms

namespace Lax369799Proofs.FiniteCoverFamilies
set_option backward.isDefEq.respectTransparency false
open Lax369799
open RankedSystems (RankedSet)
open FinitePresentations FiniteSyntacticAlgebra FiniteContextualOrder FiniteAcceptance
open ExpandedSyntacticAlgebra PresentationCovers

open Lax369799.FiniteCoverFamilies

private def pattern {A : RankedSet} {m : ℕ} (T : Fin m → FiniteSystem A 0) :
    FiniteSystem (FiniteSystem A) 0 where
  size := m
  graph := {
    label := fun i => ⟨0, T i⟩
    initial := Set.univ
    root := ∅
    edge := fun _ _ _ => False
    direction_valid := fun _ _ _ => False.elim }

private def rawCover {A : RankedSet} {m : ℕ} {T : Fin m → FiniteSystem A 0}
    {P : FiniteSystem A 0} (F : JointCover T P) :
    Cover (flattenPresentation (pattern T).graph) P.graph where
  toFun := fun v => (F.map v.1).toFun v.2
  label := fun v => (F.map v.1).label v.2
  initial := fun v h => (F.map v.1).initial v.2 h.2
  root := fun v h => h.elim ((F.map v.1).root v.2) (fun h => False.elim h.1)
  edge := by
    intro v d t ht
    rcases ht with ⟨w, hw, rfl⟩ | ⟨i, _, _⟩
    · exact (F.map v.1).edge v.2 d (.inl w) hw
    · exact Fin.elim0 i
  initial_lift := by
    intro v hv
    obtain ⟨i, w, hw, he⟩ := F.initials v hv
    exact ⟨⟨i, w⟩, ⟨True.intro, hw⟩, he⟩
  root_lift := by
    intro v hv
    obtain ⟨i, w, hw, he⟩ := F.roots v hv
    exact ⟨⟨i, w⟩, Or.inl hw, he⟩
  edge_lift := by
    intro v d t ht
    obtain ⟨s, hs, he⟩ := F.edges v.1 v.2 d t ht
    cases s with
    | inl w => exact ⟨.inl ⟨v.1, w⟩, Or.inl ⟨w, hs, rfl⟩, he⟩
    | inr j => exact Fin.elim0 j

private def constantCover {A : RankedSet} {m : ℕ} (hm : 0 < m) (p : A 0) :
    Cover (withLabels (pattern (fun _ : Fin m => atomic p)) (fun _ => p)).graph
      (atomic p).graph where
  toFun := fun _ => (0 : Fin 1)
  label := fun _ => rfl
  initial := fun _ _ => True.intro
  root := fun _ => False.elim
  edge := fun _ _ _ => False.elim
  initial_lift := fun w _ => ⟨⟨0, hm⟩, True.intro, Subsingleton.elim (α := Fin 1) _ _⟩
  root_lift := fun _ => False.elim
  edge_lift := by rintro v d t ⟨j, _, _⟩; exact Fin.elim0 j

/--
---
conclusion: Lax369799.FiniteCoverFamilies.acceptance
---
The accepting filter has a least element. Monotonicity accepts the
closed disjoint family, whose surjective cover transfers its evaluation
to the target while retaining all vertices.
-/
theorem acceptance {A : RankedSet} (L : Algebras.Language A)
    [Finite (Carrier (Accepting L) 0)] (E : SyntacticAlgebra L)
    {m : ℕ} (hm : 0 < m) (T : Fin m → FiniteSystem (Carrier (Accepting L)) 0)
    (P : FiniteSystem (Carrier (Accepting L)) 0) (F : JointCover T P)
    (hT : ∀ i, AcceptingClass (Accepting L) (E.algebra.eval 0 (T i))) :
    AcceptingClass (Accepting L) (E.algebra.eval 0 P) := by
  classical
  obtain ⟨p, hp⟩ := FiniteOrderedAlgebra.principal_acceptance L E.algebra E.evaluates inferInstance
  have hpp : AcceptingClass (Accepting L) p :=
    (hp p).mpr ((FiniteContextualOrder.class_order (Accepting L) 0).1 p)
  let Q := pattern T
  let c := fun _ : Q.Vertex => p
  let q := fun i : Q.Vertex => E.algebra.eval 0 (T i)
  have hmono := FiniteSyntacticAlgebra.evaluation_monotone (Accepting L)
    (FiniteAcceptance.accepting_isomorphic L) E.algebra E.evaluates Q c q (fun i => (hp _).mp (hT i))
  have hconst : E.algebra.eval 0 (withLabels Q c) = p := by
    have h := FiniteOuterMorphisms.evaluation_cover L E.algebra E.evaluates (constantCover hm p)
      (fun w => ⟨⟨0, hm⟩, Subsingleton.elim (α := Fin 1) _ _⟩)
    exact h.trans (E.algebra.unit 0 p)
  rw [hconst] at hmono
  have hacc := (FiniteSyntacticAlgebra.accepting_classes (Accepting L)
    (FiniteAcceptance.accepting_isomorphic L)).2 _ _ hpp hmono
  have he : withLabels Q q = relabel E.algebra.eval Q := rfl
  rw [he, E.algebra.associative] at hacc
  let e := Fintype.equivFin ((i : Fin m) × (T i).Vertex)
  let f := FiniteCovers.compose
    (FiniteCovers.isoCover (UntrimmedFlattening.isoSymm (UntrimmedFlattening.reindexIso _ e))) (rawCover F)
  have hsurj : Function.Surjective f.toFun := by
    intro v
    obtain ⟨i, w, he⟩ := F.vertices v
    refine ⟨e ⟨i, w⟩, ?_⟩
    change (F.map (e.symm (e ⟨i, w⟩)).1).toFun (e.symm (e ⟨i, w⟩)).2 = v
    rw [e.symm_apply_apply]
    exact he
  rwa [FiniteOuterMorphisms.evaluation_cover L E.algebra E.evaluates
    (S := flatten Q) (T := P) f hsurj] at hacc

end Lax369799Proofs.FiniteCoverFamilies
