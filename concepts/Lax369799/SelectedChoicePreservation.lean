import Lax369799.ExtremalUnaryTypes
import Lax369799.ChoicePreservingUnary

/-!
---
title: Choice preservation of extremally selected unary types
type: theorem
---
Rank-one extremal selection makes acceptance in normal contexts a
principal test on their data. The data for a sum of closed continuations
are the meet of the separate data. Contextual order separation therefore
gives preservation of binary choices by every selected unary type.
-/
namespace Lax369799.SelectedChoicePreservation
open RankedSystems (RankedSet)
open FiniteContextualOrder FiniteAcceptance ExpandedSyntacticAlgebra

axiom selected_preserves_choices {A : RankedSet} (L : Algebras.Language A)
    (E : SyntacticAlgebra L) (b : Carrier (Accepting L) 1)
    (hb : ExtremalUnaryTypes.Selected L E b) :
    ChoicePreservingUnary.PreservesChoices E.algebra b

end Lax369799.SelectedChoicePreservation
