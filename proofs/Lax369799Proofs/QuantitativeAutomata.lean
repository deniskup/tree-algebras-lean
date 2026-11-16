import Lax369799.QuantitativeAutomata
import Lax369799.QuantitativeWordConditions
import Lax369799Proofs.QuantitativeProfiles
import Lax369799Proofs.QuantitativeWordConditions
import Lax369799Proofs.CloneNormalization

set_option backward.isDefEq.respectTransparency false
namespace Lax369799Proofs.QuantitativeAutomata
open Lax369799
open RankedSystems (RankedSet System)
open FinitePresentations SetSystemAlgebras TransitionEncoding UnfoldAutomata
open FiniteContextualOrder FiniteAcceptance FiniteSyntacticAlgebra ExpandedSyntacticAlgebra
open Lax369799.QuantitativeAutomata

/--
---
conclusion: Lax369799.QuantitativeAutomata.automaton_bound
---
Use the bounded-profile codes to bound the two syntactic sorts and the
quantitative linked-pair construction for the branch condition. Clone
normalization changes only the transition table, preserving these bounds.
-/
theorem automaton_bound {P : Type} [Finite P]
    (L : Algebras.Language (TransitionAlphabet P))
    (hL : ∀ S T,RankedBisimilar S T → (S ∈ L ↔ T ∈ L))
    (f : ℕ → ℕ) (hA : QuantitativeRecognition.Bound f L) :
    ∃ M : UnfoldAutomaton (TransitionAlphabet P),
      BisimAutomata.IsBisimAutomaton M ∧ Recognizes M L ∧
      M.unary ≤ unaryBound f ∧ M.nullary ≤ nullaryBound f ∧
      M.condition.states ≤ stateBound f ∧ (∀ q,M.condition.priority q ≤ priorityBound f) := by
  classical
  have hAcopy := hA
  obtain ⟨B,G,η,F,hB,hr,_⟩ := hAcopy
  have hrec : Algebras.Recognizable L := ⟨B,G,η,F,hB,hr⟩
  have hinv : Algebras.UnfoldInvariantLanguage L := fun S T h => hL S T (.rel _ _ (.inl h))
  let : Finite (Carrier (Accepting L) 1) := BoundedProfileRefinement.finite_carrier_recognizable L hinv hrec 1
  let : Finite (Carrier (Accepting L) 0) := BoundedProfileRefinement.finite_carrier_recognizable L hinv hrec 0
  let : Fintype (Carrier (Accepting L) 1) := Fintype.ofFinite _
  let : Fintype (Carrier (Accepting L) 0) := Fintype.ofFinite _
  have hu : Fintype.card (Carrier (Accepting L) 1) ≤ unaryBound f := by
    exact (Nat.card_eq_fintype_card.symm.trans_le (QuantitativeProfiles.syntactic_bound L hinv f hA 1))
  have hz : Fintype.card (Carrier (Accepting L) 0) ≤ nullaryBound f := by
    exact (Nat.card_eq_fintype_card.symm.trans_le (QuantitativeProfiles.syntactic_bound L hinv f hA 0))
  obtain ⟨E⟩ := ExpandedSyntacticAlgebra.syntactic_algebra_exists L
  obtain ⟨ES,hES⟩ := SetSystemAlgebras.syntactic_structure L E
  obtain ⟨D,hfin,hinf,hs,hp⟩ := QuantitativeWordConditions.exists_condition E.algebra
    {a | AcceptingClass (Accepting L) a} (unaryBound f) (nullaryBound f) hu hz
  have hD : RunAcceptance.WordCorrect L E D := ⟨hfin,hinf⟩
  refine ⟨CloneNormalization.machine L E ES D,CloneTransitions.clone_automaton _ _ _,?_,hu,hz,hs,hp⟩
  intro S
  constructor
  · intro hS
    obtain ⟨r,hr⟩ := CloneNormalization.complete L E ES hES D hL hrec hD S hS
    exact ⟨S,(MorphismTheorems.unfold_equivalence _ _).refl S.val,r,hr⟩
  · rintro ⟨U,hU,r,hr⟩
    exact (hinv S U hU).mpr (CloneNormalization.sound L E ES hES D hL hrec hD U r hr)

end Lax369799Proofs.QuantitativeAutomata
