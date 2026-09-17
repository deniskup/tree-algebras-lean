import Lax369799.FinitePlant
import Lax369799Proofs.FiniteCovers
import Lax369799Proofs.PlantAcceptance

namespace Lax369799Proofs.FinitePlant
open Lax369799.RankedSystems (RankedSet)
open Lax369799.FinitePresentations Lax369799.FiniteAcceptance
open Lax369799.PresentationCovers
open Lax369799Proofs.Pullbacks

private theorem accepting_restriction {A : RankedSet} (L : Lax369799.Algebras.Language A)
    (S : Lax369799.RankedSystems.SetSystem A 0) :
    Accepting L (ofSetSystem S) ↔ Lax369799.SyntacticOrder.Accepting L S := by
  let f : Map S.graph S.graph := {
    toFun := id
    initial := fun _ h => h
    root := fun _ h => h
    label := fun _ => rfl
    edge := by intro v d t h; cases t <;> exact h }
  have hf := project_surjective f (fun v h => ⟨v, h, rfl⟩)
    (fun v h => ⟨v, h, rfl⟩) (fun v d t h => ⟨t, h, by cases t <;> rfl⟩)
  exact Acceptance.accepting_unfold L _ _
    ⟨_, ⟨MorphismTheorems.identity _, MorphismTheorems.identity_surjective _⟩, ⟨project f, hf⟩⟩

private noncomputable def plantProjection {A : RankedSet} {n : ℕ} (S : FiniteSystem A n) :
    Cover (ofSetSystem (Lax369799.RankedSystems.plant (Lax369799.RankedSystems.trim S.graph))).graph
      (plant S).graph where
  toFun := (FiniteAcceptance.trimProjection S.graph).toFun
  label := (FiniteAcceptance.trimProjection S.graph).label
  initial := fun _ h => False.elim h
  root := fun v h => h.elim
    (fun h => Or.inl ((FiniteAcceptance.trimProjection S.graph).root v h))
    (fun h => Or.inr ((FiniteAcceptance.trimProjection S.graph).initial v h))
  edge := (FiniteAcceptance.trimProjection S.graph).edge
  initial_lift := fun _ h => False.elim h
  root_lift := by
    intro v hv
    rcases hv with hv | hv
    · obtain ⟨w, hw, he⟩ := (FiniteAcceptance.trimProjection S.graph).root_lift v hv
      exact ⟨w, Or.inl hw, he⟩
    · obtain ⟨w, hw, he⟩ := (FiniteAcceptance.trimProjection S.graph).initial_lift v hv
      exact ⟨w, Or.inr hw, he⟩
  edge_lift := (FiniteAcceptance.trimProjection S.graph).edge_lift

/--
---
conclusion: Lax369799.FinitePlant.accepting_plant
---
The reachable restriction covers the original presentation before and
after planting. Transfer the yield-based planting law along these covers.
-/
theorem accepting_plant {A : RankedSet} (L : Lax369799.Algebras.Language A)
    (S : FiniteSystem A 0) : Accepting L (plant S) ↔ Accepting L S := by
  exact (FiniteCovers.accepting_cover L (plantProjection S)).symm.trans
    ((accepting_restriction L _).trans (PlantAcceptance.accepting_plant L _))

open Lax369799.RankedSystems (Presentation)
open Lax369799Proofs.UntrimmedFlattening

private def plantGraph {A : RankedSet} {n : ℕ} {V : Type} (G : Presentation A n V) :
    Presentation A n V := { G with initial := ∅, root := G.root ∪ G.initial }

def plantIso {A : RankedSet} {n : ℕ} {V W : Type}
    {G : Presentation A n V} {H : Presentation A n W} (f : PresentationIso G H) :
    PresentationIso (plantGraph G) (plantGraph H) where
  vertex := f.vertex
  label := f.label
  initial := fun _ => Iff.rfl
  root := fun v => or_congr (f.root v) (f.initial v)
  edge := f.edge

private def flattenPlantGraph {A : RankedSet} {n : ℕ} (S : FiniteSystem (FiniteSystem A) n) :
    PresentationIso (flattenPresentation (plant S).graph) (plantGraph (flattenPresentation S.graph)) where
  vertex := Equiv.refl _
  label := fun _ => rfl
  initial := by intro v; change False ↔ False ∧ _; simp
  root := by
    intro v
    change ((_ ∨ (_ ∧ _)) ∨ (_ ∧ _)) ↔ (_ ∨ ((_ ∨ _) ∧ _))
    tauto
  edge := by intro v d t; cases t <;> rfl

/--
---
conclusion: Lax369799.FinitePlant.flatten_plant
---
At a substituted vertex the root condition is an inner root, or an inner
initial vertex below an outer root or initial vertex. The two orders of
planting and substitution give the same condition.
-/
theorem flatten_plant {A : RankedSet} {n : ℕ} (S : FiniteSystem (FiniteSystem A) n) :
    Isomorphic (flatten (plant S)) (plant (flatten S)) := by
  classical
  exact ⟨isoTrans (isoSymm (reindexIso _ (Fintype.equivFin _)))
    (isoTrans (flattenPlantGraph S) (plantIso (reindexIso _ (Fintype.equivFin _))))⟩

/--
---
conclusion: Lax369799.FinitePlant.accepting_evaluation_plant
---
Choose a presentation representative for every quotient label. Evaluation
is the class of their substitution. Planting commutes with substitution
and preserves the acceptance test of that class.
-/
theorem accepting_evaluation_plant {A : RankedSet} (L : Lax369799.Algebras.Language A)
    (E : Lax369799.FiniteSyntacticAlgebra.Algebra (Lax369799.FiniteContextualOrder.Carrier (Accepting L)))
    (hE : ∀ n (S : FiniteSystem (FiniteSystem A) n),
      E.eval n (relabel (Lax369799.FiniteContextualOrder.quotientMap (Accepting L)) S) =
        Lax369799.FiniteContextualOrder.quotientMap (Accepting L) n (flatten S))
    (P : FiniteSystem (Lax369799.FiniteContextualOrder.Carrier (Accepting L)) 0) :
    Lax369799.FiniteSyntacticAlgebra.AcceptingClass (Accepting L) (E.eval 0 (plant P)) ↔
      Lax369799.FiniteSyntacticAlgebra.AcceptingClass (Accepting L) (E.eval 0 P) := by
  let F := Accepting L
  let rep : Lax369799.RankedSystems.RankedMap
      (Lax369799.FiniteContextualOrder.Carrier F) (FiniteSystem A) := fun _ a => a.out
  have he (Q : FiniteSystem (Lax369799.FiniteContextualOrder.Carrier F) 0) :
      E.eval 0 Q = Lax369799.FiniteContextualOrder.quotientMap F 0 (flatten (relabel rep Q)) :=
    FiniteSyntacticAlgebra.evaluation_by_representatives F E hE Q
  rw [he (plant P), he P]
  have ha := (FiniteSyntacticAlgebra.accepting_classes F (FiniteAcceptance.accepting_isomorphic L)).1
  rw [ha, ha]
  exact (FiniteAcceptance.accepting_isomorphic L _ _ (flatten_plant (relabel rep P))).trans
    (accepting_plant L _)

end Lax369799Proofs.FinitePlant
