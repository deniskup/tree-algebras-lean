import Lax369799.UnfoldAutomata
import Lax369799.TransitionEncoding
import Mathlib.Data.Fin.Basic

/-!
---
title: Bisim-automata
type: definition
---
An unfold-automaton over the transition alphabet is a bisim-automaton when
its transitions are closed under uniformly duplicating every component a
positive number of times. Thus a transition of arity n with types
(b₁,…,bₙ) entails a transition of arity nm with m consecutive copies of
each bᵢ. Nullary transitions are unchanged. This is the duplication
condition of Section 6.4; it is distinct from invariance of the recognised
language.
-/

namespace Lax369799.BisimAutomata
open RankedSystems Algebras UnfoldAutomata TransitionEncoding

def Duplicate {H : Type} {n m : ℕ} (b : Fin n → H) : Fin (n * m) → H :=
  fun i => b i.divNat

def IsBisimAutomaton {P : Type} (M : UnfoldAutomaton (TransitionAlphabet P)) : Prop :=
  ∀ (ν : Set P) (n : ℕ) (b : Fin (n + 1) → Fin M.unary),
    b ∈ M.transition n ν → ∀ m, 0 < m →
      ∃ (k : ℕ) (h : (n + 1) * m = k + 1),
        (fun i => Duplicate b (Fin.cast h.symm i)) ∈ M.transition k ν

end Lax369799.BisimAutomata
