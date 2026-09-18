import Lax369799.DeterministicElements
import Lax369799.UnfoldAutomata

/-!
---
title: Algebraic transition tables for unfold-automata
type: theorem
---
Unary and nullary algebra elements serve as edge and leaf types. A
positive-arity transition is allowed precisely when the parallel unary
value lies below the letter value. The automaton property and unary
normal form give an allowed transition preserving acceptance in each
accepting context. The word condition is supplied separately.
-/
namespace Lax369799.AlgebraicTransitions
open RankedSystems SetAlgebras AutomatonProperty UnfoldAutomata

noncomputable def decodeTypes {B : RankedSet} [Fintype (B 1)] {n : ℕ}
    (b : Fin n → Fin (Fintype.card (B 1))) : Fin n → B 1 :=
  fun i => (Fintype.equivFin (B 1)).symm (b i)

noncomputable def automaton {A B : RankedSet} [Fintype (B 1)] [Fintype (B 0)]
    (E : SetAlgebra B) (η : RankedMap A B)
    (D : WordCondition (Fintype.card (B 1)) (Fintype.card (B 0))) : UnfoldAutomaton A where
  unary := Fintype.card (B 1)
  nullary := Fintype.card (B 0)
  transition := fun n a => {b | Below E
    (E.eval (n + 1) (DeterministicElements.parallel (decodeTypes b))) (η (n + 1) a)}
  leafTransition := fun a => {(Fintype.equivFin (B 0)) (η 0 a)}
  condition := D

axiom accepting_transition {A B : RankedSet} [Fintype (B 1)] [Fintype (B 0)]
    (E : SetAlgebra B) (f : B 0) (hE : HasAutomatonProperty E f) (η : RankedMap A B)
    (D : WordCondition (Fintype.card (B 1)) (Fintype.card (B 0)))
    (n : ℕ) (a : A (n + 1)) (C : Flattening.SetContext B (n + 1) 0)
    (h : Below E f (E.eval 0 (Flattening.plug C (atomic (η (n + 1) a))))) :
    ∃ b ∈ (automaton E η D).transition n a,
      Below E f (E.eval 0 (Flattening.plug C
        (atomic (E.eval (n + 1) (DeterministicElements.parallel (decodeTypes b))))))

end Lax369799.AlgebraicTransitions
