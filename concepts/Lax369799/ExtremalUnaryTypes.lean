import Lax369799.ExpandedSyntacticAlgebra
import Lax369799.SplitExtremal

/-!
---
title: Unary types selected by extremal refinement
type: theorem
---
Unary values can themselves be refined by the extremal construction.
The selected types retain acceptance in a prescribed context and lie
below the original value. Their tests in normal contexts are principal
filters of the unary context data.
-/
namespace Lax369799.ExtremalUnaryTypes
open RankedSystems (RankedSet)
open FinitePresentations FiniteContexts FiniteContextualOrder FiniteAcceptance
open FiniteSyntacticAlgebra ExpandedSyntacticAlgebra FiniteExtremal
open ExtremalContexts (Data)

def Selected {A : RankedSet} (L : Algebras.Language A) (E : SyntacticAlgebra L)
    (b : Carrier (Accepting L) 1) : Prop :=
  ∃ (a : Carrier (Accepting L) 1) (x : Data (Carrier (Accepting L)) 1),
    IsExtremal (Accepting L) E.algebra a x ∧
      b = E.algebra.eval 1 (SplitExtremal.delta x.1 x.2 a)

axiom replacement {A : RankedSet} (L : Algebras.Language A)
    (hL : Algebras.UnfoldInvariantLanguage L) (hrec : Algebras.Recognizable L)
    (E : SyntacticAlgebra L) (C : Context (Carrier (Accepting L)) 1 0)
    (a : Carrier (Accepting L) 1)
    (ha : AcceptingClass (Accepting L) (E.algebra.eval 0 (plug C (atomic a)))) :
    ∃ b, Selected L E b ∧ ClassBelow (Accepting L) b a ∧
      AcceptingClass (Accepting L) (E.algebra.eval 0 (plug C (atomic b)))

axiom normal_test {A : RankedSet} (L : Algebras.Language A) (E : SyntacticAlgebra L)
    (b : Carrier (Accepting L) 1) (hb : Selected L E b) :
    ∃ x : Data (Carrier (Accepting L)) 1, ∀ y,
      Accepts (Accepting L) E.algebra b y ↔ DataBelow (Accepting L) x y

end Lax369799.ExtremalUnaryTypes
