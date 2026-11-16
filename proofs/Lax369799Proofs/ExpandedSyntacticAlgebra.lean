import Lax369799.ExpandedSyntacticAlgebra
import Lax369799Proofs.ExpandedContinuity
import Lax369799Proofs.FiniteAutomatonProperty
import Lax369799Proofs.FiniteResolutionNormalForms

namespace Lax369799Proofs.ExpandedSyntacticAlgebra
open Lax369799.RankedSystems (RankedSet SetSystem System trim)
open Lax369799.FinitePresentations Lax369799.FiniteContextualOrder Lax369799.FiniteAcceptance
open Lax369799.FiniteSyntacticAlgebra Lax369799.ExpandedContinuity
open Lax369799.ExpandedSyntacticAlgebra

/--
---
conclusion: Lax369799.ExpandedSyntacticAlgebra.syntactic_algebra_exists
---
Equip the contextual substitution algebra with expanded continuity.
Every lower bound is represented by a finite presentation.
-/
theorem syntactic_algebra_exists {A : RankedSet} (L : Lax369799.Algebras.Language A) :
    Nonempty (SyntacticAlgebra L) := by
  obtain ⟨E, hE⟩ := FiniteAcceptance.syntactic_substitution_algebra L
  refine ⟨⟨E, hE, ?_⟩⟩
  intro n P q hq a
  induction a using Quot.inductionOn with
  | h R => exact ExpandedContinuity.yield_lower_bound L E hE P q hq R

/--
---
conclusion: Lax369799.ExpandedSyntacticAlgebra.representatives_exist
---
Choose a representative of each vertex label in the quotient.
-/
theorem representatives_exist {A : RankedSet} (L : Lax369799.Algebras.Language A) {n : ℕ}
    (P : FiniteSystem (Carrier (Accepting L)) n) :
    ∃ q : Representatives L P, Represents L P q := by
  classical
  have h : ∀ v : P.Vertex, ∃ S : FiniteSystem A (P.graph.label v).1,
      quotientMap (Accepting L) _ S = (P.graph.label v).2 := by
    intro v
    exact Quot.exists_rep _
  exact ⟨fun v => Classical.choose (h v), fun v => Classical.choose_spec (h v)⟩

/--
---
conclusion: Lax369799.ExpandedSyntacticAlgebra.recognition
---
Acceptance descends to classes and agrees with the language on deterministic systems.
-/
theorem recognition {A : RankedSet} (L : Lax369799.Algebras.Language A)
    (hL : Lax369799.Algebras.UnfoldInvariantLanguage L) (T : System A 0) :
    AcceptingClass (Accepting L) (quotientMap (Accepting L) 0 (ofSetSystem T.val)) ↔ T ∈ L :=
  ((FiniteSyntacticAlgebra.accepting_classes (Accepting L)
    (FiniteAcceptance.accepting_isomorphic L)).1 _).trans (FiniteAcceptance.accepting_system L hL T)

/--
---
conclusion: Lax369799.ExpandedSyntacticAlgebra.expanded_normal_form
---
Apply the finite resolution normal form to the fully expanded presentation.
The retained components contain the branching choices of the representatives.
-/
theorem expanded_normal_form {A B : RankedSet} (L : Lax369799.Algebras.Language A)
    (E : SyntacticAlgebra L) (D : Lax369799.Algebras.Algebra B)
    (hD : Lax369799.Algebras.UnfoldInvariant D) (hB : Lax369799.RankedSystems.RankwiseFinite B)
    (η : Lax369799.RankedSystems.RankedMap A B) (F : Set (B 0))
    (hL : Lax369799.Algebras.Recognizes D η F L) {n : ℕ}
    (P : FiniteSystem (Carrier (Accepting L)) n)
    (q : Representatives L P) (hq : Represents L P q) :
    ∃ (k : ℕ) (c : Fin k → Lax369799.FiniteResolutionNormalForms.Component (trim (expansion L P q).graph)),
      E.algebra.eval n P = quotientMap (Accepting L) n (Lax369799.FiniteResolutionNormalForms.family c) := by
  obtain ⟨k, c, hc⟩ := FiniteResolutionNormalForms.contextual_normal_form D hD hB η F L hL (expansion L P q)
  exact ⟨k, c, (ExpandedContinuity.evaluation L E.algebra E.evaluates P q hq).trans hc⟩

/--
---
conclusion: Lax369799.ExpandedSyntacticAlgebra.automaton_property
---
The extremal argument uses substitution and contextual order, so it applies
to the algebra with expanded continuity without unary distributivity.
-/
theorem automaton_property {A : RankedSet} (L : Lax369799.Algebras.Language A)
    (hL : Lax369799.Algebras.UnfoldInvariantLanguage L) (hrec : Lax369799.Algebras.Recognizable L)
    (E : SyntacticAlgebra L) {k : ℕ}
    (C : Lax369799.FiniteContexts.Context (Carrier (Accepting L)) k 0) (a : Carrier (Accepting L) k)
    (ha : AcceptingClass (Accepting L) (E.algebra.eval 0 (Lax369799.FiniteContexts.plug C (atomic a)))) :
    ∃ δ, Lax369799.FiniteExtremal.Deterministic E.algebra δ ∧ ClassBelow (Accepting L) δ a ∧
      AcceptingClass (Accepting L) (E.algebra.eval 0 (Lax369799.FiniteContexts.plug C (atomic δ))) :=
  FiniteAutomatonProperty.recognizable_automaton_property L hL hrec E.algebra E.evaluates C a ha

/--
---
conclusion: Lax369799.ExpandedSyntacticAlgebra.expanded_yield_order
---
-/
theorem expanded_yield_order {A : RankedSet} (L : Lax369799.Algebras.Language A)
    (E : SyntacticAlgebra L) {n : ℕ}
    (P Q : FiniteSystem (Carrier (Accepting L)) n)
    (p : Representatives L P) (q : Representatives L Q)
    (hp : Represents L P p) (hq : Represents L Q q)
    (h : Lax369799.Morphisms.YieldBelow (trim (expansion L P p).graph) (trim (expansion L Q q).graph)) :
    ClassBelow (Accepting L) (E.algebra.eval n Q) (E.algebra.eval n P) := by
  apply (E.continuity P p hp _).mpr
  have hb := (E.continuity Q q hq _).mp
    ((FiniteContextualOrder.class_order (Accepting L) n).1 (E.algebra.eval n Q))
  intro T hT
  exact hb T (h T hT)

/--
---
conclusion: Lax369799.ExpandedSyntacticAlgebra.syntactic_automaton_property
---
-/
theorem syntactic_automaton_property {A : RankedSet} (L : Lax369799.Algebras.Language A)
    (hL : Lax369799.Algebras.UnfoldInvariantLanguage L) (hrec : Lax369799.Algebras.Recognizable L) :
    ∃ E : SyntacticAlgebra L, ∀ {k : ℕ}
      (C : Lax369799.FiniteContexts.Context (Carrier (Accepting L)) k 0) (a : Carrier (Accepting L) k),
      AcceptingClass (Accepting L) (E.algebra.eval 0 (Lax369799.FiniteContexts.plug C (atomic a))) →
      ∃ δ, Lax369799.FiniteExtremal.Deterministic E.algebra δ ∧ ClassBelow (Accepting L) δ a ∧
        AcceptingClass (Accepting L) (E.algebra.eval 0 (Lax369799.FiniteContexts.plug C (atomic δ))) := by
  obtain ⟨E⟩ := syntactic_algebra_exists L
  exact ⟨E, fun C a ha => automaton_property L hL hrec E C a ha⟩

end Lax369799Proofs.ExpandedSyntacticAlgebra
