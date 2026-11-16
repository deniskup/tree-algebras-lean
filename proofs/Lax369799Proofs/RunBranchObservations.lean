import Lax369799Proofs.FinitePathEvaluation
import Lax369799.RunBranchObservations
import Lax369799Proofs.RunPresentations

namespace Lax369799Proofs.RunBranchObservations
set_option backward.isDefEq.respectTransparency false
open Lax369799.RankedSystems (RankedSet System)
open Lax369799.FinitePresentations Lax369799.FiniteContextualOrder Lax369799.FiniteAcceptance
open Lax369799.FiniteSyntacticAlgebra Lax369799.ExpandedSyntacticAlgebra Lax369799.UnfoldAutomata
open Lax369799.ExpandedTransitions Lax369799.RunPresentations Lax369799.RunBranchObservations

variable {A : RankedSet} (L : Lax369799.Algebras.Language A)
    [Fintype (Carrier (Accepting L) 1)] [Fintype (Carrier (Accepting L) 0)]
    (E : SyntacticAlgebra L)
    (D : WordCondition (Fintype.card (Carrier (Accepting L) 1))
      (Fintype.card (Carrier (Accepting L) 0)))
    {S : System A 0} (r : Labelling (Fintype.card (Carrier (Accepting L) 1))
      (Fintype.card (Carrier (Accepting L) 0)) S)

private theorem internal_exists (v : S.val.Vertex) (i : Fin (Rank S v)) :
    ∃ w : (piece L E D r v).Vertex,
      (piece L E D r v).graph.label w =
        ⟨1, (Fintype.equivFin (Carrier (Accepting L) 1)).symm (r.edgeType v i)⟩ ∧
      (piece L E D r v).graph.initial w ∧
      (piece L E D r v).graph.edge w 0 (.inr i) := by
  have h : Rank S v ≠ 0 := by have := i.isLt; omega
  rw [show piece L E D r v = ofSetSystem (Lax369799.DeterministicElements.parallel
    (fun j => (Fintype.equivFin (Carrier (Accepting L) 1)).symm (r.edgeType v j))) by
      simp only [piece, if_neg h]]
  exact ⟨i, rfl, trivial, rfl, rfl⟩

private theorem leaf_exists (v : S.val.Vertex) (h : Rank S v = 0) :
    ∃ w : (piece L E D r v).Vertex,
      (piece L E D r v).graph.label w =
        ⟨0, (Fintype.equivFin (Carrier (Accepting L) 0)).symm (r.leafType v h)⟩ ∧
      (piece L E D r v).graph.initial w := by
  rw [show piece L E D r v = atomic (runLabel L E D r v) by simp only [piece, if_pos h]]
  refine ⟨(0 : Fin 1), ?_, trivial⟩
  change (⟨Rank S v, runLabel L E D r v⟩ : Lax369799.RankedSystems.Symbol _) = _
  unfold runLabel
  rw [dif_pos h]
  exact Sigma.ext h (by simp)

/--
---
conclusion: Lax369799.RunBranchObservations.path_morphism
---
The vertex at a branch step is the parallel component selected by that
step's direction. The terminal vertex is the atomic leaf component.
-/
theorem path_morphism {k : ℕ} (b : FiniteBranch S k) :
    Nonempty (Lax369799.FiniteMorphisms.Morphism (path L E D r b) (presentation L E D r)) := by
  classical
  let G := (withLabels (ofSetSystem S.val) (piece L E D r)).graph
  let f : Fin (k + 1) → (v : S.val.Vertex) × (piece L E D r v).Vertex :=
    Fin.lastCases
      ⟨b.vertex (Fin.last k), (leaf_exists L E D r _ b.ends).choose⟩
      (fun i => ⟨b.vertex i.castSucc, (internal_exists L E D r _ (b.direction i)).choose⟩)
  have outer (j : Fin (k + 1)) : (f j).1 = b.vertex j := by
    refine Fin.lastCases ?_ (fun i => ?_) j <;> simp [f]
  have ini (j : Fin (k + 1)) : (piece L E D r (f j).1).graph.initial (f j).2 := by
    let I : ((v : S.val.Vertex) × (piece L E D r v).Vertex) → Prop :=
      fun w => (piece L E D r w.1).graph.initial w.2
    change I (f j)
    refine Fin.lastCases ?_ (fun i => ?_) j
    · rw [show f (Fin.last k) = ⟨b.vertex (Fin.last k), (leaf_exists L E D r _ b.ends).choose⟩ by simp only [f, Fin.lastCases_last]]
      exact (leaf_exists L E D r _ b.ends).choose_spec.2
    · rw [show f i.castSucc = ⟨b.vertex i.castSucc, (internal_exists L E D r _ (b.direction i)).choose⟩ by simp only [f, Fin.lastCases_castSucc]]
      exact (internal_exists L E D r _ (b.direction i)).choose_spec.2.1
  apply Nonempty.intro
  apply FiniteMorphisms.toEnumeration (G := flattenPresentation G)
  refine {
    toFun := f
    initial := ?_
    root := fun _ h => False.elim h
    label := ?_
    edge := ?_ }
  · intro j hj
    have hj' : j = (0 : Fin (k + 1)) := hj
    subst j
    refine ⟨?_, ini 0⟩
    change S.val.graph.initial (f 0).1
    rw [outer]
    exact b.starts
  · intro j
    refine Fin.lastCases ?_ (fun i => ?_) j
    · simpa only [flattenPresentation, G, withLabels, ofSetSystem, Inner,
        f, Fin.lastCases_last, path] using (leaf_exists L E D r _ b.ends).choose_spec.1
    · simpa only [flattenPresentation, G, withLabels, ofSetSystem, Inner,
        f, Fin.lastCases_castSucc, path] using
        (internal_exists L E D r _ (b.direction i)).choose_spec.1
  · rintro j d t ⟨i, rfl, rfl, rfl⟩
    change (flattenPresentation G).edge (f i.castSucc) 0 (.inl (f i.succ))
    rw [show f i.castSucc = ⟨b.vertex i.castSucc, (internal_exists L E D r _ (b.direction i)).choose⟩ by simp only [f, Fin.lastCases_castSucc]]
    apply Or.inr
    refine ⟨b.direction i, (internal_exists L E D r _ (b.direction i)).choose_spec.2.2,
      Or.inl ⟨f i.succ, ?_, ini i.succ, rfl⟩⟩
    change S.val.graph.edge (b.vertex i.castSucc) (b.direction i).val (.inl (f i.succ).1)
    rw [outer]
    exact b.follows i

/--
---
conclusion: Lax369799.RunBranchObservations.path_accepting
---
Apply the presentation morphism observation principle to the branch path.
-/
theorem path_accepting
    (hr : AcceptingClass (Accepting L) (E.algebra.eval 0
      (withLabels (ofSetSystem S.val) (runLabel L E D r))))
    {k : ℕ} (b : FiniteBranch S k) :
    AcceptingClass (Accepting L) (E.algebra.eval 0 (path L E D r b)) := by
  obtain ⟨f⟩ := path_morphism L E D r b
  exact RunPresentations.observation_accepting L E D r hr _ f

/--
---
conclusion: Lax369799.RunBranchObservations.regularPath_morphism
---
Each vertex selects one outgoing component. Its successor is mapped to
the component selected at the next input vertex, including around cycles.
-/
theorem regularPath_morphism (b : RegularBranch S) :
    Nonempty (Lax369799.FiniteMorphisms.Morphism
      (regularPath L E D r b) (presentation L E D r)) := by
  classical
  let G := (withLabels (ofSetSystem S.val) (piece L E D r)).graph
  let f : Fin b.size → (v : S.val.Vertex) × (piece L E D r v).Vertex :=
    fun i => ⟨b.vertex i, (internal_exists L E D r _ (b.direction i)).choose⟩
  apply Nonempty.intro
  apply FiniteMorphisms.toEnumeration (G := flattenPresentation G)
  refine {
    toFun := f
    initial := ?_
    root := fun _ h => False.elim h
    label := fun i => (internal_exists L E D r _ (b.direction i)).choose_spec.1
    edge := ?_ }
  · intro i hi
    have hi' : i = b.start := hi
    subst i
    exact ⟨b.starts, (internal_exists L E D r _ (b.direction b.start)).choose_spec.2.1⟩
  · rintro i d t ⟨rfl, rfl⟩
    exact Or.inr ⟨b.direction i,
      (internal_exists L E D r _ (b.direction i)).choose_spec.2.2,
      Or.inl ⟨f (b.next i), b.follows i,
        (internal_exists L E D r _ (b.direction (b.next i))).choose_spec.2.1, rfl⟩⟩

/--
---
conclusion: Lax369799.RunBranchObservations.regularPath_accepting
---
Regular branch observations inherit acceptance by their presentation map.
-/
theorem regularPath_accepting
    (hr : AcceptingClass (Accepting L) (E.algebra.eval 0
      (withLabels (ofSetSystem S.val) (runLabel L E D r))))
    (b : RegularBranch S) :
    AcceptingClass (Accepting L) (E.algebra.eval 0 (regularPath L E D r b)) := by
  obtain ⟨f⟩ := regularPath_morphism L E D r b
  exact RunPresentations.observation_accepting L E D r hr _ f

/--
---
conclusion: Lax369799.RunBranchObservations.path_evaluation
---
The direct branch graph is the finite path graph of its decoded letters.
-/
theorem path_evaluation {A : RankedSet} (L : Lax369799.Algebras.Language A)
    [Fintype (Carrier (Accepting L) 1)] [Fintype (Carrier (Accepting L) 0)]
    (E : SyntacticAlgebra L)
    (D : WordCondition (Fintype.card (Carrier (Accepting L) 1))
      (Fintype.card (Carrier (Accepting L) 0)))
    {S : System A 0} (r : Labelling (Fintype.card (Carrier (Accepting L) 1))
      (Fintype.card (Carrier (Accepting L) 0)) S)
    {k : ℕ} (b : FiniteBranch S k) :
    E.algebra.eval 0 (path L E D r b) = Lax369799.FiniteBranchWords.value E.algebra
      (List.ofFn (fun i => (Fintype.equivFin (Carrier (Accepting L) 1)).symm
        (r.edgeType (b.vertex i.castSucc) (b.direction i))))
      ((Fintype.equivFin (Carrier (Accepting L) 0)).symm
        (r.leafType (b.vertex (Fin.last k)) b.ends)) :=
  FinitePathEvaluation.evaluation E.algebra _ _

end Lax369799Proofs.RunBranchObservations
