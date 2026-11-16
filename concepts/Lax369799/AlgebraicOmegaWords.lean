import Lax369799.UnaryFactorization
import Lax369799.OmegaProducts

/-!
---
title: The algebraic condition on infinite branch words
type: theorem
---
Section 6.3 accepts an infinite unary word when it belongs to V_a(V_e)^ω
for a linked pair (a,e) whose lasso evaluates to an accepting nullary
value. For a finite unary sort this language is recognized by a finite
deterministic parity word automaton.
-/

namespace Lax369799.AlgebraicOmegaWords
open RankedSystems (RankedSet)
open FiniteSyntacticAlgebra UnaryComposition UnaryFactorization UnfoldAutomata

def Accepts {A : RankedSet} (E : Algebra A) (F : Set (A 0)) (w : ℕ → A 1) : Prop :=
  ∃ (a e : A 1) (cut : ℕ → ℕ), E.eval 0 (lasso a e) ∈ F ∧
    product E e e = e ∧ product E a e = a ∧ StrictMono cut ∧ 0 < cut 0 ∧
    block E w 0 (cut 0) = a ∧ ∀ i, block E w (cut i) (cut (i + 1)) = e

axiom regular {A : RankedSet} (E : Algebra A) (F : Set (A 0)) [Fintype (A 1)] {z : ℕ} :
    ∃ D : WordCondition (Fintype.card (A 1)) z, ∀ w, D.AcceptsInfinite w ↔
      Accepts E F (fun n => (Fintype.equivFin (A 1)).symm (w n))

axiom recurrent_factorization {A : RankedSet} (E : Algebra A) (F : Set (A 0))
    {V : Type} [Finite V] (w : ℕ → A 1) (v : ℕ → V) (h : Accepts E F w) :
    ∃ (a e : A 1) (c : ℕ → ℕ) (r : V), E.eval 0 (lasso a e) ∈ F ∧
      product E e e = e ∧ product E a e = a ∧ StrictMono c ∧ 0 < c 0 ∧
      (∀ i, v (c i) = r) ∧ (∀ i, block E w 0 (c i) = a) ∧
      (∀ i j, i < j → block E w (c i) (c j) = e)

end Lax369799.AlgebraicOmegaWords
