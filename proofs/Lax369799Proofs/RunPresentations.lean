import Lax369799.RunPresentations
import Lax369799Proofs.ExpandedTransitions
import Lax369799Proofs.GraphChoices

namespace Lax369799Proofs.RunPresentations
open Lax369799.RankedSystems (RankedSet System)
open Lax369799.FinitePresentations Lax369799.FiniteContextualOrder Lax369799.FiniteAcceptance
open Lax369799.FiniteSyntacticAlgebra Lax369799.ExpandedSyntacticAlgebra Lax369799.UnfoldAutomata
open Lax369799.ExpandedTransitions Lax369799.RunPresentations

/--
---
conclusion: Lax369799.RunPresentations.evaluation
---
-/
theorem evaluation {A : RankedSet} (L : Lax369799.Algebras.Language A)
    [Fintype (Carrier (Accepting L) 1)] [Fintype (Carrier (Accepting L) 0)]
    (E : SyntacticAlgebra L)
    (D : WordCondition (Fintype.card (Carrier (Accepting L) 1))
      (Fintype.card (Carrier (Accepting L) 0)))
    {S : System A 0} (r : Labelling (Fintype.card (Carrier (Accepting L) 1))
      (Fintype.card (Carrier (Accepting L) 0)) S) :
    E.algebra.eval 0 (presentation L E D r) =
      E.algebra.eval 0 (withLabels (ofSetSystem S.val) (runLabel L E D r)) := by
  have hp : ∀ v, E.algebra.eval _ (piece L E D r v) = runLabel L E D r v := by
    intro v
    unfold piece
    split_ifs with hv
    · exact E.algebra.unit _ _
    · unfold runLabel
      rw [dif_neg hv]
  have h : relabel E.algebra.eval (withLabels (ofSetSystem S.val) (piece L E D r)) =
      withLabels (ofSetSystem S.val) (runLabel L E D r) := by
    dsimp only [relabel, withLabels]
    congr 1
    congr 1
    funext v
    exact congrArg (Sigma.mk (Rank S v)) (hp v)
  exact (E.algebra.associative _ _).symm.trans (congrArg (E.algebra.eval 0) h)

private def LowRank {A : RankedSet} {n : ℕ} (T : FiniteSystem A n) : Prop :=
  ∀ w, (T.graph.label w).1 ≤ 1

/--
---
conclusion: Lax369799.RunPresentations.unary
---
-/
theorem unary {A : RankedSet} (L : Lax369799.Algebras.Language A)
    [Fintype (Carrier (Accepting L) 1)] [Fintype (Carrier (Accepting L) 0)]
    (E : SyntacticAlgebra L)
    (D : WordCondition (Fintype.card (Carrier (Accepting L) 1))
      (Fintype.card (Carrier (Accepting L) 0)))
    {S : System A 0} (r : Labelling (Fintype.card (Carrier (Accepting L) 1))
      (Fintype.card (Carrier (Accepting L) 0)) S) :
    ∀ v, ((presentation L E D r).graph.label v).1 ≤ 1 := by
  have hp (v : S.val.Vertex) : LowRank (piece L E D r v) := by
    unfold piece
    split_ifs with hv
    · intro w
      change Rank S v ≤ 1
      omega
    · intro w
      exact Nat.le_refl 1
  intro w
  let u := (Fintype.equivFin ((v : S.val.Vertex) × (piece L E D r v).Vertex)).symm w
  exact hp u.1 u.2

/--
---
conclusion: Lax369799.RunPresentations.observation_accepting
---
-/
theorem observation_accepting {A : RankedSet} (L : Lax369799.Algebras.Language A)
    [Fintype (Carrier (Accepting L) 1)] [Fintype (Carrier (Accepting L) 0)]
    (E : SyntacticAlgebra L)
    (D : WordCondition (Fintype.card (Carrier (Accepting L) 1))
      (Fintype.card (Carrier (Accepting L) 0)))
    {S : System A 0} (r : Labelling (Fintype.card (Carrier (Accepting L) 1))
      (Fintype.card (Carrier (Accepting L) 0)) S)
    (hr : AcceptingClass (Accepting L) (E.algebra.eval 0
      (withLabels (ofSetSystem S.val) (runLabel L E D r))))
    (T : FiniteSystem (Carrier (Accepting L)) 0)
    (f : Lax369799.FiniteMorphisms.Morphism T (presentation L E D r)) :
    AcceptingClass (Accepting L) (E.algebra.eval 0 T) := by
  rw [← evaluation L E D r] at hr
  exact (FiniteSyntacticAlgebra.accepting_classes (Accepting L)
    (FiniteAcceptance.accepting_isomorphic L)).2 _ _ hr
    (FiniteOuterMorphisms.evaluation_morphism L E.algebra E.evaluates f)

private def SelectedUnary {A : RankedSet} (L : Lax369799.Algebras.Language A)
    (E : SyntacticAlgebra L) {n : ℕ} (T : FiniteSystem (Carrier (Accepting L)) n) : Prop :=
  ∀ w (h : (T.graph.label w).1 = 1), Lax369799.ExtremalUnaryTypes.Selected L E (h ▸ (T.graph.label w).2)

/--
---
conclusion: Lax369799.RunPresentations.selected
---
The unary labels in the flattened presentation are precisely the edge
types of legal transitions; nullary pieces cannot contribute unary labels.
-/
theorem selected {A : RankedSet} (L : Lax369799.Algebras.Language A)
    [Fintype (Carrier (Accepting L) 1)] [Fintype (Carrier (Accepting L) 0)]
    (E : SyntacticAlgebra L)
    (D : WordCondition (Fintype.card (Carrier (Accepting L) 1))
      (Fintype.card (Carrier (Accepting L) 0)))
    {S : System A 0} (r : Run (automaton L E D) S) :
    ∀ v (h : ((presentation L E D r.toLabelling).graph.label v).1 = 1),
      Lax369799.ExtremalUnaryTypes.Selected L E (h ▸ ((presentation L E D r.toLabelling).graph.label v).2) := by
  have he (v : S.val.Vertex) (i : Fin (Rank S v)) :
      Lax369799.ExtremalUnaryTypes.Selected L E
        ((Fintype.equivFin (Carrier (Accepting L) 1)).symm (r.edgeType v i)) := by
    have hn : Rank S v ≠ 0 := by have := i.isLt; omega
    obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero hn
    exact (r.transitions v n hn).1 (Fin.cast hn i)
  have hp (v : S.val.Vertex) : SelectedUnary L E (piece L E D r.toLabelling v) := by
    unfold piece
    split_ifs with hv
    · intro w h
      change Rank S v = 1 at h
      omega
    · intro w h
      exact he v w
  intro w h
  let u := (Fintype.equivFin ((v : S.val.Vertex) × (piece L E D r.toLabelling v).Vertex)).symm w
  exact hp u.1 u.2 h

/--
---
conclusion: Lax369799.RunPresentations.functional_test
---
All unary labels are selected. Finite choice splitting therefore applies
to the run presentation, including its cycles and retained vertices.
-/
theorem functional_test {A : RankedSet} (L : Lax369799.Algebras.Language A)
    [Fintype (Carrier (Accepting L) 1)] [Fintype (Carrier (Accepting L) 0)]
    (E : SyntacticAlgebra L)
    (D : WordCondition (Fintype.card (Carrier (Accepting L) 1))
      (Fintype.card (Carrier (Accepting L) 0)))
    {S : System A 0} (r : Run (automaton L E D) S) :
    AcceptingClass (Accepting L) (E.algebra.eval 0
      (withLabels (ofSetSystem S.val) (runLabel L E D r.toLabelling))) ↔
    ∀ f : (presentation L E D r.toLabelling).Vertex → (presentation L E D r.toLabelling).Vertex,
      Lax369799.GraphChoices.Admissible (presentation L E D r.toLabelling) f →
      AcceptingClass (Accepting L) (E.algebra.eval 0
        (Lax369799.GraphChoices.chooseRows (presentation L E D r.toLabelling) Finset.univ f)) := by
  rw [← evaluation L E D r.toLabelling]
  exact GraphChoices.admissible_test L E (presentation L E D r.toLabelling)
    (unary L E D r.toLabelling) (selected L E D r)

end Lax369799Proofs.RunPresentations
