import Lax369799.ExpandedContinuity
import Lax369799Proofs.FiniteAcceptance
import Lax369799Proofs.FiniteEvaluation
import Lax369799Proofs.FiniteContinuityOrder
import Lax369799Proofs.FiniteYieldMeets

set_option backward.isDefEq.respectTransparency false
namespace Lax369799Proofs.ExpandedContinuity
open Lax369799.RankedSystems (RankedSet)
open Lax369799.FinitePresentations Lax369799.FiniteContexts Lax369799.FiniteContextualOrder
open Lax369799.FiniteSyntacticAlgebra Lax369799.FiniteAcceptance Lax369799.ExpandedContinuity

/--
---
conclusion: Lax369799.ExpandedContinuity.evaluation
---
The chosen representatives relabel to the original pattern, so the
quotient evaluation law applies directly to their simultaneous expansion.
-/
theorem evaluation {A : RankedSet} (L : Lax369799.Algebras.Language A)
    (E : Algebra (Carrier (Accepting L)))
    (hE : ∀ n (S : FiniteSystem (FiniteSystem A) n),
      E.eval n (relabel (quotientMap (Accepting L)) S) = quotientMap (Accepting L) n (flatten S))
    {n : ℕ} (P : FiniteSystem (Carrier (Accepting L)) n)
    (q : Representatives L P) (hq : Represents L P q) :
    E.eval n P = quotientMap (Accepting L) n (expansion L P q) := by
  have hp : relabel (quotientMap (Accepting L)) (withLabels P q) = P := by
    dsimp only [relabel, withLabels]
    congr 1
    congr 1
    funext v
    exact (congrArg (Sigma.mk (P.graph.label v).1) (hq v)).trans (Sigma.eta _)
  have h := hE n (withLabels P q)
  rw [hp] at h
  exact h

/--
---
conclusion: Lax369799.ExpandedContinuity.closed_continuity
---
Acceptance of the evaluated class is precisely acceptance of all initial
and root yields of the expanded closed presentation.
-/
theorem closed_continuity {A : RankedSet} (L : Lax369799.Algebras.Language A)
    (E : Algebra (Carrier (Accepting L)))
    (hE : ∀ n (S : FiniteSystem (FiniteSystem A) n),
      E.eval n (relabel (quotientMap (Accepting L)) S) = quotientMap (Accepting L) n (flatten S))
    (P : FiniteSystem (Carrier (Accepting L)) 0)
    (q : Representatives L P) (hq : Represents L P q) :
    AcceptingClass (Accepting L) (E.eval 0 P) ↔
      ∀ T, Lax369799.Morphisms.Yield (Lax369799.RankedSystems.trim (expansion L P q).graph) T → Admissible L T := by
  rw [evaluation L E hE P q hq]
  exact (FiniteSyntacticAlgebra.accepting_classes (Accepting L) (FiniteAcceptance.accepting_isomorphic L)).1 _

/--
---
conclusion: Lax369799.ExpandedContinuity.contextual_continuity
---
The contextual order tests acceptance after plugging the expansion in each
base-alphabet context. Yields are taken after this complete substitution.
-/
theorem contextual_continuity {A : RankedSet} (L : Lax369799.Algebras.Language A)
    (E : Algebra (Carrier (Accepting L)))
    (hE : ∀ n (S : FiniteSystem (FiniteSystem A) n),
      E.eval n (relabel (quotientMap (Accepting L)) S) = quotientMap (Accepting L) n (flatten S))
    {n : ℕ} (P : FiniteSystem (Carrier (Accepting L)) n)
    (q : Representatives L P) (hq : Represents L P q) (R : FiniteSystem A n) :
    ClassBelow (Accepting L) (quotientMap (Accepting L) n R) (E.eval n P) ↔
      ∀ C : Context A n 0, Accepting L (plug C R) →
        ∀ T, ResolvesIn L P q C T → Admissible L T := by
  rw [evaluation L E hE P q hq]
  rfl

/--
---
conclusion: Lax369799.ExpandedContinuity.representative_independence
---
All choices of representatives give the same evaluated class, hence the
same acceptance tests in every context. Equality of individual yield sets
is not required.
-/
theorem representative_independence {A : RankedSet} (L : Lax369799.Algebras.Language A)
    (E : Algebra (Carrier (Accepting L)))
    (hE : ∀ n (S : FiniteSystem (FiniteSystem A) n),
      E.eval n (relabel (quotientMap (Accepting L)) S) = quotientMap (Accepting L) n (flatten S))
    {n : ℕ} (P : FiniteSystem (Carrier (Accepting L)) n)
    (q r : Representatives L P) (hq : Represents L P q) (hr : Represents L P r)
    (C : Context A n 0) :
    (∀ T, ResolvesIn L P q C T → Admissible L T) ↔
      (∀ T, ResolvesIn L P r C T → Admissible L T) := by
  have he := (evaluation L E hE P q hq).symm.trans (evaluation L E hE P r hr)
  have ho := FiniteContextualOrder.class_order (Accepting L) n
  have hqr : Below (Accepting L) (expansion L P q) (expansion L P r) := by
    change ClassBelow (Accepting L) (quotientMap (Accepting L) n (expansion L P q))
      (quotientMap (Accepting L) n (expansion L P r))
    rw [he]
    exact ho.1 _
  have hrq : Below (Accepting L) (expansion L P r) (expansion L P q) := by
    change ClassBelow (Accepting L) (quotientMap (Accepting L) n (expansion L P r))
      (quotientMap (Accepting L) n (expansion L P q))
    rw [he]
    exact ho.1 _
  exact ⟨hqr C, hrq C⟩

/--
---
conclusion: Lax369799.ExpandedContinuity.finite_approximation
---
Identify evaluation with the class of the expanded representative, then
apply finite yield approximation of the contextual order. Finite sums
are retained before applying any surrounding context.
-/
theorem finite_approximation {A : RankedSet} (L : Lax369799.Algebras.Language A)
    (E : Algebra (Carrier (Accepting L)))
    (hE : ∀ n (S : FiniteSystem (FiniteSystem A) n),
      E.eval n (relabel (quotientMap (Accepting L)) S) = quotientMap (Accepting L) n (flatten S))
    {n : ℕ} (P : FiniteSystem (Carrier (Accepting L)) n)
    (q : Representatives L P) (hq : Represents L P q) (R : FiniteSystem A n) :
    ClassBelow (Accepting L) (quotientMap (Accepting L) n R) (E.eval n P) ↔
      ∀ (m : ℕ) (F : Fin m → Lax369799.RankedSystems.SetSystem A n),
        (∀ i, Lax369799.Morphisms.Yield (Lax369799.RankedSystems.trim (expansion L P q).graph) (F i)) →
        ClassBelow (Accepting L) (quotientMap (Accepting L) n R)
          (quotientMap (Accepting L) n (ofSetSystem (Lax369799.YieldContinuity.finiteSum F))) := by
  rw [evaluation L E hE P q hq]
  exact FiniteContinuityOrder.order_approximation L R (expansion L P q)

/--
---
conclusion: Lax369799.ExpandedContinuity.yield_lower_bound
---
Expand the representatives before taking yields. Finite sums are meets
in the contextual order, so the finite approximation criterion is
equivalent to being below every individual yield of the expansion.
-/
theorem yield_lower_bound {A : RankedSet} (L : Lax369799.Algebras.Language A)
    (E : Algebra (Carrier (Accepting L)))
    (hE : ∀ n (S : FiniteSystem (FiniteSystem A) n),
      E.eval n (relabel (quotientMap (Accepting L)) S) = quotientMap (Accepting L) n (flatten S))
    {n : ℕ} (P : FiniteSystem (Carrier (Accepting L)) n)
    (q : Representatives L P) (hq : Represents L P q) (R : FiniteSystem A n) :
    ClassBelow (Accepting L) (quotientMap (Accepting L) n R) (E.eval n P) ↔
      ∀ T : Lax369799.RankedSystems.SetSystem A n,
        Lax369799.Morphisms.Yield (Lax369799.RankedSystems.trim (expansion L P q).graph) T →
        ClassBelow (Accepting L) (quotientMap (Accepting L) n R)
          (quotientMap (Accepting L) n (ofSetSystem T)) := by
  rw [evaluation L E hE P q hq]
  exact FiniteYieldMeets.yield_lower_bound L R (expansion L P q)

end Lax369799Proofs.ExpandedContinuity
