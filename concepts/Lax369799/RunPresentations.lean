import Lax369799.ExpandedTransitions
import Lax369799.GraphChoices

/-!
---
title: Unary presentations associated with legal runs
type: theorem
---
Replace each internal vertex by its chosen parallel tuple and each leaf by
its nullary value, then flatten. The resulting unary/nullary presentation
has the value of the evaluated run. Its path and cycle observations inherit
acceptance through presentation morphisms.
-/
namespace Lax369799.RunPresentations
open RankedSystems (RankedSet System)
open FinitePresentations FiniteContextualOrder FiniteAcceptance FiniteSyntacticAlgebra
open ExpandedSyntacticAlgebra UnfoldAutomata ExpandedTransitions

noncomputable def piece {A : RankedSet} (L : Algebras.Language A)
    [Fintype (Carrier (Accepting L) 1)] [Fintype (Carrier (Accepting L) 0)]
    (E : SyntacticAlgebra L)
    (D : WordCondition (Fintype.card (Carrier (Accepting L) 1))
      (Fintype.card (Carrier (Accepting L) 0)))
    {S : System A 0} (r : Labelling (Fintype.card (Carrier (Accepting L) 1))
      (Fintype.card (Carrier (Accepting L) 0)) S) (v : S.val.Vertex) :
    FiniteSystem (Carrier (Accepting L)) (Rank S v) :=
  if Rank S v = 0 then atomic (runLabel L E D r v)
  else ofSetSystem (DeterministicElements.parallel
    (fun i => (Fintype.equivFin (Carrier (Accepting L) 1)).symm (r.edgeType v i)))

noncomputable def presentation {A : RankedSet} (L : Algebras.Language A)
    [Fintype (Carrier (Accepting L) 1)] [Fintype (Carrier (Accepting L) 0)]
    (E : SyntacticAlgebra L)
    (D : WordCondition (Fintype.card (Carrier (Accepting L) 1))
      (Fintype.card (Carrier (Accepting L) 0)))
    {S : System A 0} (r : Labelling (Fintype.card (Carrier (Accepting L) 1))
      (Fintype.card (Carrier (Accepting L) 0)) S) : FiniteSystem (Carrier (Accepting L)) 0 :=
  flatten (withLabels (ofSetSystem S.val) (piece L E D r))

axiom evaluation {A : RankedSet} (L : Algebras.Language A)
    [Fintype (Carrier (Accepting L) 1)] [Fintype (Carrier (Accepting L) 0)]
    (E : SyntacticAlgebra L)
    (D : WordCondition (Fintype.card (Carrier (Accepting L) 1))
      (Fintype.card (Carrier (Accepting L) 0)))
    {S : System A 0} (r : Labelling (Fintype.card (Carrier (Accepting L) 1))
      (Fintype.card (Carrier (Accepting L) 0)) S) :
    E.algebra.eval 0 (presentation L E D r) =
      E.algebra.eval 0 (withLabels (ofSetSystem S.val) (runLabel L E D r))

axiom unary {A : RankedSet} (L : Algebras.Language A)
    [Fintype (Carrier (Accepting L) 1)] [Fintype (Carrier (Accepting L) 0)]
    (E : SyntacticAlgebra L)
    (D : WordCondition (Fintype.card (Carrier (Accepting L) 1))
      (Fintype.card (Carrier (Accepting L) 0)))
    {S : System A 0} (r : Labelling (Fintype.card (Carrier (Accepting L) 1))
      (Fintype.card (Carrier (Accepting L) 0)) S) :
    ∀ v, ((presentation L E D r).graph.label v).1 ≤ 1

axiom observation_accepting {A : RankedSet} (L : Algebras.Language A)
    [Fintype (Carrier (Accepting L) 1)] [Fintype (Carrier (Accepting L) 0)]
    (E : SyntacticAlgebra L)
    (D : WordCondition (Fintype.card (Carrier (Accepting L) 1))
      (Fintype.card (Carrier (Accepting L) 0)))
    {S : System A 0} (r : Labelling (Fintype.card (Carrier (Accepting L) 1))
      (Fintype.card (Carrier (Accepting L) 0)) S)
    (hr : AcceptingClass (Accepting L) (E.algebra.eval 0
      (withLabels (ofSetSystem S.val) (runLabel L E D r))))
    (T : FiniteSystem (Carrier (Accepting L)) 0)
    (f : FiniteMorphisms.Morphism T (presentation L E D r)) :
    AcceptingClass (Accepting L) (E.algebra.eval 0 T)

axiom selected {A : RankedSet} (L : Algebras.Language A)
    [Fintype (Carrier (Accepting L) 1)] [Fintype (Carrier (Accepting L) 0)]
    (E : SyntacticAlgebra L)
    (D : WordCondition (Fintype.card (Carrier (Accepting L) 1))
      (Fintype.card (Carrier (Accepting L) 0)))
    {S : System A 0} (r : Run (automaton L E D) S) :
    ∀ v (h : ((presentation L E D r.toLabelling).graph.label v).1 = 1),
      ExtremalUnaryTypes.Selected L E (h ▸ ((presentation L E D r.toLabelling).graph.label v).2)

axiom functional_test {A : RankedSet} (L : Algebras.Language A)
    [Fintype (Carrier (Accepting L) 1)] [Fintype (Carrier (Accepting L) 0)]
    (E : SyntacticAlgebra L)
    (D : WordCondition (Fintype.card (Carrier (Accepting L) 1))
      (Fintype.card (Carrier (Accepting L) 0)))
    {S : System A 0} (r : Run (automaton L E D) S) :
    AcceptingClass (Accepting L) (E.algebra.eval 0
      (withLabels (ofSetSystem S.val) (runLabel L E D r.toLabelling))) ↔
    ∀ f : (presentation L E D r.toLabelling).Vertex → (presentation L E D r.toLabelling).Vertex,
      GraphChoices.Admissible (presentation L E D r.toLabelling) f →
      AcceptingClass (Accepting L) (E.algebra.eval 0
        (GraphChoices.chooseRows (presentation L E D r.toLabelling) Finset.univ f))

end Lax369799.RunPresentations
