import Lax369799.BisimAutomata
import Lax369799.FiniteRecurrence
import Lax369799.FiniteAlgebraMeets
import Mathlib.Logic.Equiv.Fin.Basic

/-!
---
title: Compressed transitions and their clone closure
type: theorem
---
Lemma 108 compresses each block of directions by taking the meet of its
unary labels, retains the compressed tuples occurring infinitely often,
and closes them under uniform duplication. The closure is a clone table,
and one threshold controls all compressed transition families appearing
in a finite input system.
-/

namespace Lax369799.CloneTransitions
open RankedSystems (RankedSet)
open SetSystemAlgebras BisimAutomata UnfoldAutomata TransitionEncoding

def Closure {H : Type} (B : ∀ n, Set (Fin n → H)) (n : ℕ) : Set (Fin n → H) :=
  {b | ∃ p m, 0 < p ∧ 0 < m ∧ ∃ h : p * m = n,
    ∃ c ∈ B p, b = fun i => Duplicate c (Fin.cast h.symm i)}

def compress {A : RankedSet} (E : SetAlgebra A) {n k : ℕ}
    (b : Fin (n * k) → A 1) : Fin n → A 1 :=
  fun i => FiniteAlgebraMeets.value E (fun j : Fin k => b (finProdFinEquiv (i, j)))

def alpha {A : RankedSet} {V : Type} (E : SetAlgebra A)
    (T : V → ∀ n, Set (Fin (n + 1) → A 1)) (ν : V) (n k : ℕ) : Set (Fin n → A 1) :=
  {c | ∃ (l : ℕ) (h : n * k = l + 1) (b : Fin (l + 1) → A 1),
    b ∈ T ν l ∧ compress E (fun i => b (Fin.cast h i)) = c}

def beta {A : RankedSet} {V : Type} (E : SetAlgebra A)
    (T : V → ∀ n, Set (Fin (n + 1) → A 1)) (ν : V) (n : ℕ) : Set (Fin n → A 1) :=
  FiniteRecurrence.Recurrent (alpha E T ν n)

noncomputable def automaton {P H : Type} [Fintype H] {z : ℕ}
    (B : Set P → ∀ n, Set (Fin n → H)) (leaves : Set P → Set (Fin z))
    (D : WordCondition (Fintype.card H) z) : UnfoldAutomaton (TransitionAlphabet P) where
  unary := Fintype.card H
  nullary := z
  transition := fun n ν => {b | (fun i => (Fintype.equivFin H).symm (b i)) ∈ Closure (B ν) (n + 1)}
  leafTransition := leaves
  condition := D

axiom closure_closed {H : Type} (B : ∀ n, Set (Fin n → H)) {n m : ℕ}
    (b : Fin n → H) (hb : b ∈ Closure B n) (hm : 0 < m) : Duplicate b ∈ Closure B (n * m)

axiom component {A : RankedSet} (E : SetAlgebra A) {n k : ℕ}
    (b : Fin (n * k) → A 1) (i : Fin n) (j : Fin k) :
    Below E (compress E b i) (b (finProdFinEquiv (i, j)))

axiom stabilizes {A : RankedSet} {V : Type} (E : SetAlgebra A) [Finite (A 1)]
    (T : V → ∀ n, Set (Fin (n + 1) → A 1)) (ν : V) (n : ℕ) :
    ∃ N, ∀ k, N ≤ k → alpha E T ν n k ⊆ beta E T ν n

axiom uniform_stabilization {A : RankedSet} {V I : Type} (E : SetAlgebra A)
    [Finite (A 1)] [Finite I] (T : V → ∀ n, Set (Fin (n + 1) → A 1))
    (ν : I → V) (arity : I → ℕ) :
    ∃ N, ∀ i k, N ≤ k → alpha E T (ν i) (arity i) k ⊆ beta E T (ν i) (arity i)

axiom clone_automaton {P H : Type} [Fintype H] {z : ℕ}
    (B : Set P → ∀ n, Set (Fin n → H)) (leaves : Set P → Set (Fin z))
    (D : WordCondition (Fintype.card H) z) : IsBisimAutomaton (automaton B leaves D)

axiom refinement {A : RankedSet} {V : Type} (E : SetAlgebra A)
    (T : V → ∀ n, Set (Fin (n + 1) → A 1)) (ν : V) {n : ℕ}
    (b : Fin n → A 1) (hb : b ∈ Closure (beta E T ν) n) :
    ∃ (l : ℕ) (c : Fin (l + 1) → A 1), c ∈ T ν l ∧
      ∃ σ : Fin (l + 1) → Fin n, Function.Surjective σ ∧
        ∀ i, Below E (b (σ i)) (c i)

end Lax369799.CloneTransitions
