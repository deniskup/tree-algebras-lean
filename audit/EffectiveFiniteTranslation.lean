import Lax369799Proofs.MainTheorems
import Lax369799Proofs.FiniteTesting

open Lax369799

private def isolated : FiniteModelChecking.Graph (Fin 0) 0 :=
  ⟨0,(fun _ _ => false),(fun _ p => Fin.elim0 p)⟩

private def loop : FiniteModelChecking.Graph (Fin 0) 0 :=
  ⟨0,(fun _ _ => true),(fun _ p => Fin.elim0 p)⟩

private def selfEdge : MonadicSecondOrder.Sentence (Fin 0) :=
  .existsVertex (.edge 0 0)

private def infinitePath : ModalMuCalculus.Sentence (Fin 0) :=
  .nu (.diamond (.variable 0))

private def table : FiniteModalData.Data (Fin 0) 1 0 1 0 :=
  ⟨0,(fun _ _ => 0),(fun _ => 0),(fun _ => false),
    (fun _ a => Fin.elim0 a),(fun _ B => B 0)⟩

-- Finite reachability and both logical model checkers execute.
#eval FiniteTesting.valid isolated
#eval FiniteModelChecking.mso loop selfEdge
#eval FiniteModelChecking.mu isolated infinitePath
#eval FiniteModelChecking.mu loop infinitePath

-- These formulas agree on one-vertex models; a two-cycle separates them.
#eval FiniteTesting.test 1 selfEdge infinitePath
#eval FiniteTesting.test 2 selfEdge infinitePath

-- Complete table enumeration and the modal syntax compiler execute.
#eval (FiniteModalData.elements (FiniteModalData.Data (Fin 0) 0 0 1 0)).length
#eval FiniteModelChecking.mu isolated (FiniteModalData.compile table)
#eval FiniteModelChecking.mu loop (FiniteModalData.compile table)

#print axioms Lax369799.EffectiveFiniteTranslation.compile
#print axioms Lax369799Proofs.EffectiveFiniteTranslation.compile_correct
#print axioms Lax369799Proofs.MainTheorems.finite_bisimulation_invariant_mso
#print axioms Lax369799Proofs.MainTheorems.effective_finite_bisimulation_invariant_mso
