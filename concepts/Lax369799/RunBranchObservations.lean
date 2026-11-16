import Lax369799.RunPresentations
import Lax369799.FinitePathEvaluation

/-!
---
title: Finite branch observations of a run
type: theorem
---
A terminating branch determines a unary path followed by its nullary leaf.
This path maps into the flattened run presentation. Consequently an
accepted evaluated run has accepted terminating branch observations.
-/
namespace Lax369799.RunBranchObservations
open RankedSystems (RankedSet System)
open FinitePresentations FiniteContextualOrder FiniteAcceptance
open FiniteSyntacticAlgebra ExpandedSyntacticAlgebra UnfoldAutomata ExpandedTransitions

noncomputable def path {A : RankedSet} (L : Algebras.Language A)
    [Fintype (Carrier (Accepting L) 1)] [Fintype (Carrier (Accepting L) 0)]
    (E : SyntacticAlgebra L)
    (D : WordCondition (Fintype.card (Carrier (Accepting L) 1))
      (Fintype.card (Carrier (Accepting L) 0)))
    {S : System A 0} (r : Labelling (Fintype.card (Carrier (Accepting L) 1))
      (Fintype.card (Carrier (Accepting L) 0)) S)
    {k : ℕ} (b : FiniteBranch S k) : FiniteSystem (Carrier (Accepting L)) 0 where
  size := k + 1
  graph := {
    label := Fin.lastCases
      ⟨0, (Fintype.equivFin (Carrier (Accepting L) 0)).symm
        (r.leafType (b.vertex (Fin.last k)) b.ends)⟩
      (fun i => ⟨1, (Fintype.equivFin (Carrier (Accepting L) 1)).symm
        (r.edgeType (b.vertex i.castSucc) (b.direction i))⟩)
    initial := {0}
    root := ∅
    edge := fun v d t => ∃ i : Fin k, v = i.castSucc ∧ d = 0 ∧ t = .inl i.succ
    direction_valid := by
      rintro v d t ⟨i, rfl, rfl, rfl⟩
      simp }

axiom path_morphism {A : RankedSet} (L : Algebras.Language A)
    [Fintype (Carrier (Accepting L) 1)] [Fintype (Carrier (Accepting L) 0)]
    (E : SyntacticAlgebra L)
    (D : WordCondition (Fintype.card (Carrier (Accepting L) 1))
      (Fintype.card (Carrier (Accepting L) 0)))
    {S : System A 0} (r : Labelling (Fintype.card (Carrier (Accepting L) 1))
      (Fintype.card (Carrier (Accepting L) 0)) S)
    {k : ℕ} (b : FiniteBranch S k) :
    Nonempty (FiniteMorphisms.Morphism (path L E D r b) (RunPresentations.presentation L E D r))

axiom path_accepting {A : RankedSet} (L : Algebras.Language A)
    [Fintype (Carrier (Accepting L) 1)] [Fintype (Carrier (Accepting L) 0)]
    (E : SyntacticAlgebra L)
    (D : WordCondition (Fintype.card (Carrier (Accepting L) 1))
      (Fintype.card (Carrier (Accepting L) 0)))
    {S : System A 0} (r : Labelling (Fintype.card (Carrier (Accepting L) 1))
      (Fintype.card (Carrier (Accepting L) 0)) S)
    (hr : AcceptingClass (Accepting L) (E.algebra.eval 0
      (withLabels (ofSetSystem S.val) (runLabel L E D r))))
    {k : ℕ} (b : FiniteBranch S k) :
    AcceptingClass (Accepting L) (E.algebra.eval 0 (path L E D r b))

/-- A finite graph describing a regular infinite branch of the input. -/
structure RegularBranch {A : RankedSet} (S : System A 0) where
  size : ℕ
  start : Fin size
  next : Fin size → Fin size
  vertex : Fin size → S.val.Vertex
  direction : ∀ i, Fin (Rank S (vertex i))
  starts : vertex start ∈ S.val.graph.initial
  follows : ∀ i, S.val.graph.edge (vertex i) (direction i).val (.inl (vertex (next i)))

noncomputable def regularPath {A : RankedSet} (L : Algebras.Language A)
    [Fintype (Carrier (Accepting L) 1)] [Fintype (Carrier (Accepting L) 0)]
    (E : SyntacticAlgebra L)
    (D : WordCondition (Fintype.card (Carrier (Accepting L) 1))
      (Fintype.card (Carrier (Accepting L) 0)))
    {S : System A 0} (r : Labelling (Fintype.card (Carrier (Accepting L) 1))
      (Fintype.card (Carrier (Accepting L) 0)) S)
    (b : RegularBranch S) : FiniteSystem (Carrier (Accepting L)) 0 where
  size := b.size
  graph := {
    label := fun i => ⟨1, (Fintype.equivFin (Carrier (Accepting L) 1)).symm
      (r.edgeType (b.vertex i) (b.direction i))⟩
    initial := {b.start}
    root := ∅
    edge := fun v d t => d = 0 ∧ t = .inl (b.next v)
    direction_valid := by rintro v d t ⟨rfl, _⟩; exact Nat.zero_lt_one }

axiom regularPath_morphism {A : RankedSet} (L : Algebras.Language A)
    [Fintype (Carrier (Accepting L) 1)] [Fintype (Carrier (Accepting L) 0)]
    (E : SyntacticAlgebra L)
    (D : WordCondition (Fintype.card (Carrier (Accepting L) 1))
      (Fintype.card (Carrier (Accepting L) 0)))
    {S : System A 0} (r : Labelling (Fintype.card (Carrier (Accepting L) 1))
      (Fintype.card (Carrier (Accepting L) 0)) S)
    (b : RegularBranch S) :
    Nonempty (FiniteMorphisms.Morphism (regularPath L E D r b) (RunPresentations.presentation L E D r))

axiom regularPath_accepting {A : RankedSet} (L : Algebras.Language A)
    [Fintype (Carrier (Accepting L) 1)] [Fintype (Carrier (Accepting L) 0)]
    (E : SyntacticAlgebra L)
    (D : WordCondition (Fintype.card (Carrier (Accepting L) 1))
      (Fintype.card (Carrier (Accepting L) 0)))
    {S : System A 0} (r : Labelling (Fintype.card (Carrier (Accepting L) 1))
      (Fintype.card (Carrier (Accepting L) 0)) S)
    (hr : AcceptingClass (Accepting L) (E.algebra.eval 0
      (withLabels (ofSetSystem S.val) (runLabel L E D r))))
    (b : RegularBranch S) :
    AcceptingClass (Accepting L) (E.algebra.eval 0 (regularPath L E D r b))

axiom path_evaluation {A : RankedSet} (L : Algebras.Language A)
    [Fintype (Carrier (Accepting L) 1)] [Fintype (Carrier (Accepting L) 0)]
    (E : SyntacticAlgebra L)
    (D : WordCondition (Fintype.card (Carrier (Accepting L) 1))
      (Fintype.card (Carrier (Accepting L) 0)))
    {S : System A 0} (r : Labelling (Fintype.card (Carrier (Accepting L) 1))
      (Fintype.card (Carrier (Accepting L) 0)) S)
    {k : ℕ} (b : FiniteBranch S k) :
    E.algebra.eval 0 (path L E D r b) = FiniteBranchWords.value E.algebra
      (List.ofFn (fun i => (Fintype.equivFin (Carrier (Accepting L) 1)).symm
        (r.edgeType (b.vertex i.castSucc) (b.direction i))))
      ((Fintype.equivFin (Carrier (Accepting L) 0)).symm
        (r.leafType (b.vertex (Fin.last k)) b.ends))

end Lax369799.RunBranchObservations
