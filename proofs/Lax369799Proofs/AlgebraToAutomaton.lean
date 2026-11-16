import Lax369799Proofs.SupportedCompletion
import Lax369799.AlgebraToAutomaton
import Lax369799Proofs.RunAcceptance
import Lax369799Proofs.BoundedProfileRefinement
import Lax369799Proofs.UnfoldEquivalence

namespace Lax369799Proofs.AlgebraToAutomaton
open Lax369799
open RankedSystems (RankedSet)
open Algebras UnfoldAutomata FiniteContextualOrder FiniteAcceptance ExpandedSyntacticAlgebra

/--
---
conclusion: Lax369799.AlgebraToAutomaton.algebra_to_automaton
---
Use the finite unary and nullary sorts of the yield-syntactic algebra.
The linked-pair word condition makes accepting evaluated runs precisely
accepting automaton runs. Every accepted input has such a run, and
monotonicity transfers acceptance of a run back to the input.
-/
theorem algebra_to_automaton {A : RankedSet} (L : Language A)
    (hL : UnfoldInvariantLanguage L) (hA : SupportedAlgebras.Recognizable L) :
    ∃ M : UnfoldAutomaton A, UnfoldAutomata.Recognizes M L := by
  classical
  have hA : Algebras.Recognizable L := SupportedCompletion.legacy_recognizable L hA
  letI : Finite (Carrier (Accepting L) 1) := BoundedProfileRefinement.finite_carrier_recognizable L hL hA 1
  letI : Finite (Carrier (Accepting L) 0) := BoundedProfileRefinement.finite_carrier_recognizable L hL hA 0
  letI : Fintype (Carrier (Accepting L) 1) := Fintype.ofFinite _
  letI : Fintype (Carrier (Accepting L) 0) := Fintype.ofFinite _
  obtain ⟨E⟩ := ExpandedSyntacticAlgebra.syntactic_algebra_exists L
  obtain ⟨D, hD⟩ := RunAcceptance.exists_condition L E
  refine ⟨ExpandedTransitions.automaton L E D, fun S => ?_⟩
  constructor
  · intro hS
    obtain ⟨r, hr⟩ := ExpandedTransitions.evaluated_run_exists L hL hA E D S hS
    exact ⟨S, (MorphismTheorems.unfold_equivalence A 0).refl S.val, r,
      (RunAcceptance.evaluated_run_iff L E D r hL hA hD).mpr hr⟩
  · rintro ⟨T, hST, r, hr⟩
    have hT := ExpandedTransitions.evaluated_run_sound L hL E D r
      ((RunAcceptance.evaluated_run_iff L E D r hL hA hD).mp hr)
    exact (hL S T hST).mpr hT

end Lax369799Proofs.AlgebraToAutomaton
