import Lax369799.MonadicSecondOrder
import Lax369799.ModalMuCalculus

/-!
---
title: MSO translation and bisimulation invariance of the mu-calculus
type: theorem
---
Every modal mu-calculus sentence has an equivalent MSO sentence, and its
truth is preserved by bisimulation. These standard results supply the
reverse implication of the main theorem. The semantic monotonicity lemma
justifies the fixed-point clauses of the mu-calculus semantics.
-/

namespace Lax369799.MuCalculusTheorems
open TransitionSystems

axiom eval_monotone {P : Type} (S : TransitionSystem P) {n : ℕ}
    (φ : ModalMuCalculus.Formula P n) (ρ σ : Fin n → Set S.Vertex)
    (h : ∀ i, ρ i ⊆ σ i) : φ.eval S ρ ⊆ φ.eval S σ

axiom mu_to_mso {P : Type} (φ : ModalMuCalculus.Sentence P) :
  ∃ ψ : MonadicSecondOrder.Sentence P, ∀ S,
    ModalMuCalculus.Models S φ ↔ MonadicSecondOrder.Models S ψ

axiom mu_bisimulation_invariant {P : Type} (φ : ModalMuCalculus.Sentence P) :
  BisimulationInvariant {S | ModalMuCalculus.Models S φ}

end Lax369799.MuCalculusTheorems
