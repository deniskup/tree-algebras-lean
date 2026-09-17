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
arXiv:2407.12677v6. Invariance is required only between finite systems.
-/

namespace Lax369799.FiniteBisimulationTheorem
open TransitionSystems

axiom finite_bisimulation_invariant_mso {P : Type} [Finite P]
    (L : Set (TransitionSystem P)) :
    (MonadicSecondOrder.Definable L ∧ BisimulationInvariant L) ↔
      ModalMuCalculus.Definable L

end Lax369799.FiniteBisimulationTheorem
