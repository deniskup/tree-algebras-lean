import Lax369799.SupportedAlgebras
import Lax369799.UnfoldAutomata

/-!
---
title: Rankwise-finite recognition implies automaton recognition
type: theorem
---
An unfold-invariant language of systems recognised by a rankwise-finite
algebra is recognised by an unfold-automaton. This is `thm:alg2aut` in
Section 6.3. The recognising algebra in the hypothesis is not assumed to
be unfold-invariant; unfold-invariance is a property of the language.
-/

namespace Lax369799.AlgebraToAutomaton
open RankedSystems Algebras UnfoldAutomata

axiom algebra_to_automaton {A : RankedSet} (L : Language A)
    (hL : UnfoldInvariantLanguage L) (hA : SupportedAlgebras.Recognizable L) :
    ∃ M : UnfoldAutomaton A, UnfoldAutomata.Recognizes M L

end Lax369799.AlgebraToAutomaton
