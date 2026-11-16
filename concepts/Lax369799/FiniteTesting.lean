import Lax369799.FiniteModelChecking
import Lax369799.FiniteModalData

/-!
---
title: Executable bounded comparison of MSO and modal formulas
type: theorem
---
Enumerate finite Boolean graph tables up to the prescribed vertex bound.
A second-order closure test filters exactly the reachable models, and
the verified model checkers compare the two sentence semantics.
-/

namespace Lax369799.FiniteTesting
open FiniteModelChecking

def valid {P : Type} {k : ℕ} (G : Graph P k) : Bool :=
  decide (∀ X : Fin (k+1) → Bool,X G.1 = true →
    (∀ v w,X v = true → G.2.1 v w = true → X w = true) → ∀ v,X v = true)

def agree {P : Type} {k : ℕ} (G : Graph P k) (φ : MonadicSecondOrder.Sentence P)
    (ψ : ModalMuCalculus.Sentence P) : Bool :=
  if valid G then (mso G φ == mu G ψ) else true

def test {P : Type} [Fintype P] [Encodable P] [DecidableEq P] (K : ℕ)
    (φ : MonadicSecondOrder.Sentence P) (ψ : ModalMuCalculus.Sentence P) : Bool :=
  (List.range K).all (fun k => (FiniteModalData.elements (Graph P k)).all (fun G => agree G φ ψ))

open TransitionSystems

axiom test_correct {P : Type} [Fintype P] [Encodable P] [DecidableEq P] (K : ℕ)
    (φ : MonadicSecondOrder.Sentence P) (ψ : ModalMuCalculus.Sentence P) :
    test K φ ψ = true ↔ ∀ S : TransitionSystem P,S.size ≤ K →
      (MonadicSecondOrder.Models S φ ↔ ModalMuCalculus.Models S ψ)

end Lax369799.FiniteTesting