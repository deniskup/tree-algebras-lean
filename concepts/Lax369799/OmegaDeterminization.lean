import Lax369799.UnfoldAutomata

/-!
---
title: Determinization of infinite-word automata
type: theorem
---
Every nondeterministic Büchi word automaton has an equivalent finite
deterministic parity word automaton. This is the word-automaton ingredient
of Section 6.3. The parity condition uses the least recurring priority.
-/

namespace Lax369799.OmegaDeterminization
open UnfoldAutomata

structure Buchi (alphabet : ℕ) where
  states : ℕ
  initial : Set (Fin states)
  transition : Fin states → Fin alphabet → Fin states → Prop
  accepting : Set (Fin states)

def Buchi.Accepts {u : ℕ} (B : Buchi u) (w : ℕ → Fin u) : Prop :=
  ∃ r : ℕ → Fin B.states, r 0 ∈ B.initial ∧
    (∀ n, B.transition (r n) (w n) (r (n + 1))) ∧
    {n | r n ∈ B.accepting}.Infinite

axiom determinization {u z : ℕ} (B : Buchi u) :
    ∃ D : WordCondition u z, ∀ w, D.AcceptsInfinite w ↔ B.Accepts w

end Lax369799.OmegaDeterminization
