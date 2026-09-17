import Lax369799.BisimAutomata
import Lax369799.ModalMuCalculus

/-!
---
title: Bisim-automaton normal form and modal translation
type: theorem
---
A bisimulation-invariant language recognised by a rankwise-finite algebra
has a recognising bisim-automaton (`lemma:bisim-aut`, Section 6.4).
The modal translation identifies the acceptance of such an automaton with
a mu-calculus sentence when its recognised language is bisimulation-invariant.
The latter hypothesis is explicit: the duplication condition alone does
not assert language invariance.
-/

namespace Lax369799.BisimAutomatonTheorem
open RankedSystems Algebras UnfoldAutomata TransitionEncoding BisimAutomata

axiom bisim_automaton_exists {P : Type} [Finite P]
    (L : Language (TransitionAlphabet P))
    (hL : ∀ S T, RankedBisimilar S T → (S ∈ L ↔ T ∈ L))
    (hA : Recognizable L) :
    ∃ M : UnfoldAutomaton (TransitionAlphabet P),
      IsBisimAutomaton M ∧ UnfoldAutomata.Recognizes M L

axiom bisim_automaton_to_mu {P : Type} [Finite P]
    (M : UnfoldAutomaton (TransitionAlphabet P)) (hM : IsBisimAutomaton M)
    (hL : ∀ S T, RankedBisimilar S T → (Accepts M S ↔ Accepts M T)) :
    ∃ φ : ModalMuCalculus.Sentence P, ∀ S,
      Accepts M S ↔ ModalMuCalculus.Models (decode S) φ

end Lax369799.BisimAutomatonTheorem
