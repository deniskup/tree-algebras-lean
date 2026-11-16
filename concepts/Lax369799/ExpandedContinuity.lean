import Lax369799.FiniteAcceptance
import Lax369799.FiniteContinuityOrder
import Lax369799.FiniteYieldMeets

/-!
---
title: Continuity through expanded representatives
type: theorem
---
Expand every algebra-valued vertex into a representative before resolving
nondeterminism. All substitutions retain unreachable vertices until the
final yield observation. Acceptance of these expanded resolutions, also
in every surrounding context, is independent of the representatives.
This is a contextual continuity law; it does not identify the yields of
an atomic algebra-valued pattern with those of its expansion.
-/
namespace Lax369799.ExpandedContinuity
open RankedSystems (RankedSet SetSystem System)
open FinitePresentations FiniteContexts FiniteContextualOrder FiniteSyntacticAlgebra
open FiniteAcceptance

abbrev Representatives {A : RankedSet} (L : Algebras.Language A) {n : ℕ}
    (P : FiniteSystem (Carrier (Accepting L)) n) :=
  ∀ v : P.Vertex, FiniteSystem A (P.graph.label v).1

def Represents {A : RankedSet} (L : Algebras.Language A) {n : ℕ}
    (P : FiniteSystem (Carrier (Accepting L)) n) (q : Representatives L P) : Prop :=
  ∀ v, quotientMap (Accepting L) _ (q v) = (P.graph.label v).2

noncomputable def expansion {A : RankedSet} (L : Algebras.Language A) {n : ℕ}
    (P : FiniteSystem (Carrier (Accepting L)) n) (q : Representatives L P) : FiniteSystem A n :=
  flatten (withLabels P q)

def Admissible {A : RankedSet} (L : Algebras.Language A) (T : SetSystem A 0) : Prop :=
  ∃ U : System A 0, U ∈ L ∧ (T = U.val ∨ T = RankedSystems.plant U.val)

def ResolvesIn {A : RankedSet} (L : Algebras.Language A) {n : ℕ}
    (P : FiniteSystem (Carrier (Accepting L)) n) (q : Representatives L P)
    (C : Context A n 0) (T : SetSystem A 0) : Prop :=
  Morphisms.Yield (RankedSystems.trim (plug C (expansion L P q)).graph) T

axiom evaluation {A : RankedSet} (L : Algebras.Language A)
    (E : Algebra (Carrier (Accepting L)))
    (hE : ∀ n (S : FiniteSystem (FiniteSystem A) n),
      E.eval n (relabel (quotientMap (Accepting L)) S) = quotientMap (Accepting L) n (flatten S))
    {n : ℕ} (P : FiniteSystem (Carrier (Accepting L)) n)
    (q : Representatives L P) (hq : Represents L P q) :
    E.eval n P = quotientMap (Accepting L) n (expansion L P q)

axiom closed_continuity {A : RankedSet} (L : Algebras.Language A)
    (E : Algebra (Carrier (Accepting L)))
    (hE : ∀ n (S : FiniteSystem (FiniteSystem A) n),
      E.eval n (relabel (quotientMap (Accepting L)) S) = quotientMap (Accepting L) n (flatten S))
    (P : FiniteSystem (Carrier (Accepting L)) 0)
    (q : Representatives L P) (hq : Represents L P q) :
    AcceptingClass (Accepting L) (E.eval 0 P) ↔
      ∀ T, Morphisms.Yield (RankedSystems.trim (expansion L P q).graph) T → Admissible L T

axiom contextual_continuity {A : RankedSet} (L : Algebras.Language A)
    (E : Algebra (Carrier (Accepting L)))
    (hE : ∀ n (S : FiniteSystem (FiniteSystem A) n),
      E.eval n (relabel (quotientMap (Accepting L)) S) = quotientMap (Accepting L) n (flatten S))
    {n : ℕ} (P : FiniteSystem (Carrier (Accepting L)) n)
    (q : Representatives L P) (hq : Represents L P q) (R : FiniteSystem A n) :
    ClassBelow (Accepting L) (quotientMap (Accepting L) n R) (E.eval n P) ↔
      ∀ C : Context A n 0, Accepting L (plug C R) →
        ∀ T, ResolvesIn L P q C T → Admissible L T

axiom representative_independence {A : RankedSet} (L : Algebras.Language A)
    (E : Algebra (Carrier (Accepting L)))
    (hE : ∀ n (S : FiniteSystem (FiniteSystem A) n),
      E.eval n (relabel (quotientMap (Accepting L)) S) = quotientMap (Accepting L) n (flatten S))
    {n : ℕ} (P : FiniteSystem (Carrier (Accepting L)) n)
    (q r : Representatives L P) (hq : Represents L P q) (hr : Represents L P r)
    (C : Context A n 0) :
    (∀ T, ResolvesIn L P q C T → Admissible L T) ↔
      (∀ T, ResolvesIn L P r C T → Admissible L T)

axiom finite_approximation {A : RankedSet} (L : Algebras.Language A)
    (E : Algebra (Carrier (Accepting L)))
    (hE : ∀ n (S : FiniteSystem (FiniteSystem A) n),
      E.eval n (relabel (quotientMap (Accepting L)) S) = quotientMap (Accepting L) n (flatten S))
    {n : ℕ} (P : FiniteSystem (Carrier (Accepting L)) n)
    (q : Representatives L P) (hq : Represents L P q) (R : FiniteSystem A n) :
    ClassBelow (Accepting L) (quotientMap (Accepting L) n R) (E.eval n P) ↔
      ∀ (m : ℕ) (F : Fin m → SetSystem A n),
        (∀ i, Morphisms.Yield (RankedSystems.trim (expansion L P q).graph) (F i)) →
        ClassBelow (Accepting L) (quotientMap (Accepting L) n R)
          (quotientMap (Accepting L) n (ofSetSystem (YieldContinuity.finiteSum F)))

axiom yield_lower_bound {A : RankedSet} (L : Algebras.Language A)
    (E : Algebra (Carrier (Accepting L)))
    (hE : ∀ n (S : FiniteSystem (FiniteSystem A) n),
      E.eval n (relabel (quotientMap (Accepting L)) S) = quotientMap (Accepting L) n (flatten S))
    {n : ℕ} (P : FiniteSystem (Carrier (Accepting L)) n)
    (q : Representatives L P) (hq : Represents L P q) (R : FiniteSystem A n) :
    ClassBelow (Accepting L) (quotientMap (Accepting L) n R) (E.eval n P) ↔
      ∀ T : SetSystem A n,
        Morphisms.Yield (RankedSystems.trim (expansion L P q).graph) T →
        ClassBelow (Accepting L) (quotientMap (Accepting L) n R)
          (quotientMap (Accepting L) n (ofSetSystem T))

end Lax369799.ExpandedContinuity
