import Lax369799.EffectiveFiniteTranslation
import Lax369799.MonadicSecondOrder
import Lax369799.ModalMuCalculus

/-!
---
title: Bisimulation-invariant MSO on finite graphs
type: theorem
---
For a finite set of proposition letters, a property of finite reachable
transition systems is MSO-definable and bisimulation-invariant if and only
if it is definable in the modal mu-calculus. This is the main theorem
`theorem:bisim-invariant-finite` of Colcombet, Doumane and Kuperberg,
revised local manuscript of 13 November 2026. Invariance is required only between finite systems.
-/

namespace Lax369799.FiniteBisimulationTheorem
open TransitionSystems

axiom finite_bisimulation_invariant_mso {P : Type} [Finite P]
    (L : Set (TransitionSystem P)) :
    (MonadicSecondOrder.Definable L ∧ BisimulationInvariant L) ↔
      ModalMuCalculus.Definable L

/-- A total executable translation, correct under the finite-invariance promise. -/
axiom effective_finite_bisimulation_invariant_mso {P : Type}
    [Fintype P] [Encodable P] [DecidableEq P]
    (φ : MonadicSecondOrder.Sentence P)
    (hφ : BisimulationInvariant {S | MonadicSecondOrder.Models S φ}) :
    ∀ S : TransitionSystem P, MonadicSecondOrder.Models S φ ↔
      ModalMuCalculus.Models S (EffectiveFiniteTranslation.compile φ)

end Lax369799.FiniteBisimulationTheorem
