import Lax369799.ExpandedContinuity
import Lax369799.FiniteAutomatonProperty
import Lax369799.FiniteResolutionNormalForms

/-!
---
title: Syntactic algebras with expanded continuity
type: theorem
---
The syntactic quotient is a substitution algebra of finite presentations.
Its continuity law resolves base-alphabet representatives after expansion.
It applies to every lower bound and every choice of representatives.
Finite resolution normal forms retain entire branching components.
-/
namespace Lax369799.ExpandedSyntacticAlgebra
open RankedSystems (RankedSet SetSystem System trim)
open FinitePresentations FiniteContextualOrder FiniteAcceptance
open FiniteSyntacticAlgebra ExpandedContinuity

structure SyntacticAlgebra {A : RankedSet} (L : Algebras.Language A) where
  algebra : Algebra (Carrier (Accepting L))
  evaluates : ∀ n (S : FiniteSystem (FiniteSystem A) n),
    algebra.eval n (relabel (quotientMap (Accepting L)) S) =
      quotientMap (Accepting L) n (flatten S)
  continuity : ∀ {n} (P : FiniteSystem (Carrier (Accepting L)) n)
    (q : Representatives L P), Represents L P q → ∀ a : Carrier (Accepting L) n,
    ClassBelow (Accepting L) a (algebra.eval n P) ↔
      ∀ T : SetSystem A n, Morphisms.Yield (trim (expansion L P q).graph) T →
        ClassBelow (Accepting L) a (quotientMap (Accepting L) n (ofSetSystem T))

axiom syntactic_algebra_exists {A : RankedSet} (L : Algebras.Language A) :
    Nonempty (SyntacticAlgebra L)

axiom representatives_exist {A : RankedSet} (L : Algebras.Language A) {n : ℕ}
    (P : FiniteSystem (Carrier (Accepting L)) n) :
    ∃ q : Representatives L P, Represents L P q

axiom recognition {A : RankedSet} (L : Algebras.Language A)
    (hL : Algebras.UnfoldInvariantLanguage L) (T : System A 0) :
    AcceptingClass (Accepting L) (quotientMap (Accepting L) 0 (ofSetSystem T.val)) ↔ T ∈ L

axiom expanded_normal_form {A B : RankedSet} (L : Algebras.Language A)
    (E : SyntacticAlgebra L) (D : Algebras.Algebra B)
    (hD : Algebras.UnfoldInvariant D) (hB : RankedSystems.RankwiseFinite B)
    (η : RankedSystems.RankedMap A B) (F : Set (B 0))
    (hL : Algebras.Recognizes D η F L) {n : ℕ}
    (P : FiniteSystem (Carrier (Accepting L)) n)
    (q : Representatives L P) (hq : Represents L P q) :
    ∃ (k : ℕ) (c : Fin k → FiniteResolutionNormalForms.Component (trim (expansion L P q).graph)),
      E.algebra.eval n P = quotientMap (Accepting L) n (FiniteResolutionNormalForms.family c)

axiom automaton_property {A : RankedSet} (L : Algebras.Language A)
    (hL : Algebras.UnfoldInvariantLanguage L) (hrec : Algebras.Recognizable L)
    (E : SyntacticAlgebra L) {k : ℕ}
    (C : FiniteContexts.Context (Carrier (Accepting L)) k 0) (a : Carrier (Accepting L) k)
    (ha : AcceptingClass (Accepting L) (E.algebra.eval 0 (FiniteContexts.plug C (atomic a)))) :
    ∃ δ, FiniteExtremal.Deterministic E.algebra δ ∧ ClassBelow (Accepting L) δ a ∧
      AcceptingClass (Accepting L) (E.algebra.eval 0 (FiniteContexts.plug C (atomic δ)))

axiom expanded_yield_order {A : RankedSet} (L : Algebras.Language A)
    (E : SyntacticAlgebra L) {n : ℕ}
    (P Q : FiniteSystem (Carrier (Accepting L)) n)
    (p : Representatives L P) (q : Representatives L Q)
    (hp : Represents L P p) (hq : Represents L Q q)
    (h : Morphisms.YieldBelow (trim (expansion L P p).graph) (trim (expansion L Q q).graph)) :
    ClassBelow (Accepting L) (E.algebra.eval n Q) (E.algebra.eval n P)

axiom syntactic_automaton_property {A : RankedSet} (L : Algebras.Language A)
    (hL : Algebras.UnfoldInvariantLanguage L) (hrec : Algebras.Recognizable L) :
    ∃ E : SyntacticAlgebra L, ∀ {k : ℕ}
      (C : FiniteContexts.Context (Carrier (Accepting L)) k 0) (a : Carrier (Accepting L) k),
      AcceptingClass (Accepting L) (E.algebra.eval 0 (FiniteContexts.plug C (atomic a))) →
      ∃ δ, FiniteExtremal.Deterministic E.algebra δ ∧ ClassBelow (Accepting L) δ a ∧
        AcceptingClass (Accepting L) (E.algebra.eval 0 (FiniteContexts.plug C (atomic δ)))

end Lax369799.ExpandedSyntacticAlgebra
