import Lax369799.SelectedParallel
import Lax369799.AlgebraicTransitions
import Lax369799.ExpandedCertificates

/-!
---
title: Transition tables for the algebra with expanded continuity
type: theorem
---
The split extremal construction supplies parallel transitions in accepting
contexts, after rank-one refinement of every component. Legal transitions
require these selected unary types, which preserve binary choices of closed
continuations. A run assigns their values to the input vertices. Pointwise
comparison then transfers acceptance of that evaluated run to the input.
Every accepted input also admits a legal run with an accepted evaluated
value. The separate implication from a word condition to acceptance of
the run value is not assumed here.
-/
namespace Lax369799.ExpandedTransitions
open RankedSystems (RankedSet RankedMap System)
open FinitePresentations FiniteContextualOrder FiniteAcceptance FiniteSyntacticAlgebra
open ExpandedSyntacticAlgebra UnfoldAutomata

noncomputable def automaton {A : RankedSet} (L : Algebras.Language A)
    [Fintype (Carrier (Accepting L) 1)] [Fintype (Carrier (Accepting L) 0)]
    (E : SyntacticAlgebra L)
    (D : WordCondition (Fintype.card (Carrier (Accepting L) 1))
      (Fintype.card (Carrier (Accepting L) 0))) : UnfoldAutomaton A where
  unary := Fintype.card (Carrier (Accepting L) 1)
  nullary := Fintype.card (Carrier (Accepting L) 0)
  transition := fun n a => {b |
    (∀ i, ExtremalUnaryTypes.Selected L E (AlgebraicTransitions.decodeTypes b i)) ∧
    ClassBelow (Accepting L)
    (E.algebra.eval (n + 1) (ofSetSystem (DeterministicElements.parallel
      (AlgebraicTransitions.decodeTypes b)))) (quotientMap (Accepting L) _ (atomic a))}
  leafTransition := fun a => {(Fintype.equivFin (Carrier (Accepting L) 0))
    (quotientMap (Accepting L) 0 (atomic a))}
  condition := D

noncomputable def runLabel {A : RankedSet} (L : Algebras.Language A)
    [Fintype (Carrier (Accepting L) 1)] [Fintype (Carrier (Accepting L) 0)]
    (E : SyntacticAlgebra L)
    (D : WordCondition (Fintype.card (Carrier (Accepting L) 1))
      (Fintype.card (Carrier (Accepting L) 0)))
    {S : System A 0} (r : Labelling (Fintype.card (Carrier (Accepting L) 1))
      (Fintype.card (Carrier (Accepting L) 0)) S) (v : S.val.Vertex) :
    Carrier (Accepting L) (Rank S v) :=
  if h : Rank S v = 0 then h.symm ▸
    (Fintype.equivFin (Carrier (Accepting L) 0)).symm (r.leafType v h)
  else E.algebra.eval _ (ofSetSystem (DeterministicElements.parallel
    (fun i => (Fintype.equivFin (Carrier (Accepting L) 1)).symm (r.edgeType v i))))

axiom accepting_transition {A : RankedSet} (L : Algebras.Language A)
    (hL : Algebras.UnfoldInvariantLanguage L) (hrec : Algebras.Recognizable L)
    [Fintype (Carrier (Accepting L) 1)] [Fintype (Carrier (Accepting L) 0)]
    (E : SyntacticAlgebra L)
    (D : WordCondition (Fintype.card (Carrier (Accepting L) 1))
      (Fintype.card (Carrier (Accepting L) 0)))
    (n : ℕ) (a : A (n + 1)) (C : FiniteContexts.Context (Carrier (Accepting L)) (n + 1) 0)
    (ha : AcceptingClass (Accepting L) (E.algebra.eval 0 (FiniteContexts.plug C
      (atomic (quotientMap (Accepting L) _ (atomic a)))))) :
    ∃ b ∈ (automaton L E D).transition n a,
      AcceptingClass (Accepting L) (E.algebra.eval 0 (FiniteContexts.plug C
        (atomic (E.algebra.eval (n + 1) (ofSetSystem
          (DeterministicElements.parallel (AlgebraicTransitions.decodeTypes b)))))))

axiom run_label_below {A : RankedSet} (L : Algebras.Language A)
    [Fintype (Carrier (Accepting L) 1)] [Fintype (Carrier (Accepting L) 0)]
    (E : SyntacticAlgebra L)
    (D : WordCondition (Fintype.card (Carrier (Accepting L) 1))
      (Fintype.card (Carrier (Accepting L) 0)))
    {S : System A 0} (r : Run (automaton L E D) S) (v : S.val.Vertex) :
    ClassBelow (Accepting L) (runLabel L E D r.toLabelling v)
      (quotientMap (Accepting L) _ (atomic (S.val.graph.label v).2))

axiom evaluated_run_sound {A : RankedSet} (L : Algebras.Language A)
    (hL : Algebras.UnfoldInvariantLanguage L)
    [Fintype (Carrier (Accepting L) 1)] [Fintype (Carrier (Accepting L) 0)]
    (E : SyntacticAlgebra L)
    (D : WordCondition (Fintype.card (Carrier (Accepting L) 1))
      (Fintype.card (Carrier (Accepting L) 0)))
    {S : System A 0} (r : Run (automaton L E D) S)
    (hr : AcceptingClass (Accepting L)
      (E.algebra.eval 0 (withLabels (ofSetSystem S.val) (runLabel L E D r.toLabelling)))) : S ∈ L

axiom evaluated_run_exists {A : RankedSet} (L : Algebras.Language A)
    (hL : Algebras.UnfoldInvariantLanguage L) (hrec : Algebras.Recognizable L)
    [Fintype (Carrier (Accepting L) 1)] [Fintype (Carrier (Accepting L) 0)]
    (E : SyntacticAlgebra L)
    (D : WordCondition (Fintype.card (Carrier (Accepting L) 1))
      (Fintype.card (Carrier (Accepting L) 0)))
    (S : System A 0) (hS : S ∈ L) :
    ∃ r : Run (automaton L E D) S, AcceptingClass (Accepting L)
      (E.algebra.eval 0 (withLabels (ofSetSystem S.val) (runLabel L E D r.toLabelling)))

axiom edge_preserves_choices {A : RankedSet} (L : Algebras.Language A)
    [Fintype (Carrier (Accepting L) 1)] [Fintype (Carrier (Accepting L) 0)]
    (E : SyntacticAlgebra L)
    (D : WordCondition (Fintype.card (Carrier (Accepting L) 1))
      (Fintype.card (Carrier (Accepting L) 0)))
    {S : System A 0} (r : Run (automaton L E D) S) (v : S.val.Vertex) (i : Fin (Rank S v)) :
    ChoicePreservingUnary.PreservesChoices E.algebra
      ((Fintype.equivFin (Carrier (Accepting L) 1)).symm (r.edgeType v i))

end Lax369799.ExpandedTransitions
