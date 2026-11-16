import Lax369799.AlgebraicBranchCondition
import Lax369799.RunPresentations

/-!
---
title: Word acceptance and evaluation of algebraic runs
type: theorem
---
For the algebraic unfold-automaton, legal runs expand into root-free
reachable unary presentations with no blocked unary vertex. Projecting
their branches back to the input preserves the run's word labels. The
algebraic branch condition therefore makes a run accepting exactly when
the evaluated run value is accepted (Lemmas 104–105).
-/

namespace Lax369799.RunAcceptance
open RankedSystems (RankedSet System)
open FinitePresentations FiniteContextualOrder FiniteAcceptance FiniteSyntacticAlgebra
open ExpandedSyntacticAlgebra UnfoldAutomata ExpandedTransitions RunPresentations

def WordCorrect {A : RankedSet} (L : Algebras.Language A)
    [Fintype (Carrier (Accepting L) 1)] [Fintype (Carrier (Accepting L) 0)]
    (E : SyntacticAlgebra L)
    (D : WordCondition (Fintype.card (Carrier (Accepting L) 1))
      (Fintype.card (Carrier (Accepting L) 0))) : Prop :=
  (∀ w a, D.AcceptsFinite w a ↔ AcceptingClass (Accepting L)
    (FiniteBranchWords.value E.algebra (w.map (Fintype.equivFin (Carrier (Accepting L) 1)).symm)
      ((Fintype.equivFin (Carrier (Accepting L) 0)).symm a))) ∧
  (∀ w, D.AcceptsInfinite w ↔ AlgebraicOmegaWords.Accepts E.algebra
    {a | AcceptingClass (Accepting L) a}
    (fun n => (Fintype.equivFin (Carrier (Accepting L) 1)).symm (w n)))

axiom exists_condition {A : RankedSet} (L : Algebras.Language A)
    [Fintype (Carrier (Accepting L) 1)] [Fintype (Carrier (Accepting L) 0)]
    (E : SyntacticAlgebra L) :
    ∃ D : WordCondition (Fintype.card (Carrier (Accepting L) 1))
      (Fintype.card (Carrier (Accepting L) 0)), WordCorrect L E D

section
variable {A : RankedSet} (L : Algebras.Language A)
    [Fintype (Carrier (Accepting L) 1)] [Fintype (Carrier (Accepting L) 0)]
    (E : SyntacticAlgebra L)
    (D : WordCondition (Fintype.card (Carrier (Accepting L) 1))
      (Fintype.card (Carrier (Accepting L) 0)))
    {S : System A 0} (r : Run (automaton L E D) S)

axiom shape :
    (presentation L E D r.toLabelling).graph.root = ∅ ∧ Reachable (presentation L E D r.toLabelling) ∧
      ∀ v, ((presentation L E D r.toLabelling).graph.label v).1 = 1 →
        ∃ w, (presentation L E D r.toLabelling).graph.edge v 0 (.inl w)

axiom accepting_run_value (hL : Algebras.UnfoldInvariantLanguage L) (hrec : Algebras.Recognizable L)
    (hD : WordCorrect L E D) (hr : r.Accepting) :
    AcceptingClass (Accepting L) (E.algebra.eval 0
      (withLabels (ofSetSystem S.val) (runLabel L E D r.toLabelling)))

axiom evaluated_run_accepting (hD : WordCorrect L E D)
    (hr : AcceptingClass (Accepting L) (E.algebra.eval 0
      (withLabels (ofSetSystem S.val) (runLabel L E D r.toLabelling)))) : r.Accepting

axiom evaluated_run_iff (hL : Algebras.UnfoldInvariantLanguage L) (hrec : Algebras.Recognizable L)
    (hD : WordCorrect L E D) : r.Accepting ↔
    AcceptingClass (Accepting L) (E.algebra.eval 0
      (withLabels (ofSetSystem S.val) (runLabel L E D r.toLabelling)))

/-- Accepted evaluation implies word acceptance without transition legality. -/
axiom labelling_accepting (r : Labelling (Fintype.card (Carrier (Accepting L) 1))
      (Fintype.card (Carrier (Accepting L) 0)) S) (hD : WordCorrect L E D)
    (hr : AcceptingClass (Accepting L) (E.algebra.eval 0
      (withLabels (ofSetSystem S.val) (runLabel L E D r)))) : r.Accepting D

end

end Lax369799.RunAcceptance
