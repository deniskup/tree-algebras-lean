import Lax369799.DirectionProjections

/-!
---
title: The path criterion and the automaton property
type: theorem
---
A regular branch is a closed unary/nullary system admitting a morphism
into the tested set-system. Lemma 95 says that a root-free set-system
with all vertices initially reachable and with no blocked unary vertex
is accepted exactly when all its regular branches are accepted, provided
its unary labels are extremal. Together with canonical direction
decomposition this is Definition 90. Corollary 96 establishes both
conditions for the rankwise-finite yield-syntactic set-algebra.
-/

namespace Lax369799.ExtremalPaths
open RankedSystems (RankedSet System)
open FinitePresentations FiniteContextualOrder FiniteSyntacticAlgebra FiniteAcceptance
open ExpandedSyntacticAlgebra

def Unary {A : RankedSet} (P : FiniteSystem A 0) : Prop :=
  ∀ v, (P.graph.label v).1 ≤ 1

def RegularBranch {A : RankedSet} (G : FiniteSystem A 0) (B : System A 0) : Prop :=
  Unary (ofSetSystem B.val) ∧ Nonempty (FiniteMorphisms.Morphism (ofSetSystem B.val) G)

def HasAutomatonProperty {A : RankedSet} (L : Algebras.Language A) (E : SyntacticAlgebra L) : Prop :=
  (∀ k (_hk : 1 ≤ k) (a : Carrier (Accepting L) k), ExtendedContexts.ExtremalElement L E a →
    E.algebra.eval k (DirectionProjections.parallel (DirectionProjections.direction E.algebra a)) = a ∧
    ∀ i, ExtendedContexts.ExtremalElement L E (DirectionProjections.direction E.algebra a i)) ∧
  (∀ G : FiniteSystem (Carrier (Accepting L)) 0, Unary G → G.graph.root = ∅ → Reachable G →
    (∀ v, (G.graph.label v).1 = 1 → ∃ w, G.graph.edge v 0 (.inl w)) →
    (∀ v (h : (G.graph.label v).1 = 1),
      ExtendedContexts.ExtremalElement L E (h ▸ (G.graph.label v).2)) →
    (AcceptingClass (Accepting L) (E.algebra.eval 0 G) ↔
      ∀ B, RegularBranch G B → AcceptingClass (Accepting L) (E.algebra.eval 0 (ofSetSystem B.val))))

axiom path_criterion {A : RankedSet} (L : Algebras.Language A)
    (hL : Algebras.UnfoldInvariantLanguage L) (hrec : Algebras.Recognizable L)
    (E : SyntacticAlgebra L) (G : FiniteSystem (Carrier (Accepting L)) 0)
    (hu : Unary G) (hr : G.graph.root = ∅) (hreach : Reachable G)
    (ht : ∀ v, (G.graph.label v).1 = 1 → ∃ w, G.graph.edge v 0 (.inl w))
    (hs : ∀ v (h : (G.graph.label v).1 = 1),
      ExtendedContexts.ExtremalElement L E (h ▸ (G.graph.label v).2)) :
    AcceptingClass (Accepting L) (E.algebra.eval 0 G) ↔
      ∀ B : System (Carrier (Accepting L)) 0, Unary (ofSetSystem B.val) →
        Nonempty (FiniteMorphisms.Morphism (ofSetSystem B.val) G) →
        AcceptingClass (Accepting L) (E.algebra.eval 0 (ofSetSystem B.val))

axiom selected_path_criterion {A : RankedSet} (L : Algebras.Language A)
    (hL : Algebras.UnfoldInvariantLanguage L) (hrec : Algebras.Recognizable L)
    (E : SyntacticAlgebra L) (G : FiniteSystem (Carrier (Accepting L)) 0)
    (hu : Unary G) (hr : G.graph.root = ∅) (hreach : Reachable G)
    (ht : ∀ v, (G.graph.label v).1 = 1 → ∃ w, G.graph.edge v 0 (.inl w))
    (hs : ∀ v (h : (G.graph.label v).1 = 1),
      ExtremalUnaryTypes.Selected L E (h ▸ (G.graph.label v).2)) :
    AcceptingClass (Accepting L) (E.algebra.eval 0 G) ↔
      ∀ B : System (Carrier (Accepting L)) 0, Unary (ofSetSystem B.val) →
        Nonempty (FiniteMorphisms.Morphism (ofSetSystem B.val) G) →
        AcceptingClass (Accepting L) (E.algebra.eval 0 (ofSetSystem B.val))

axiom syntactic_automaton_property {A : RankedSet} (L : Algebras.Language A)
    (hL : Algebras.UnfoldInvariantLanguage L) (hrec : Algebras.Recognizable L)
    (E : SyntacticAlgebra L) : HasAutomatonProperty L E

end Lax369799.ExtremalPaths
