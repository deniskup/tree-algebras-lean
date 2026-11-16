import Mathlib.SetTheory.Cardinal.NatCard
import Lax369799.MSORecognition
import Lax369799.SetLogicTranslation

/-!
---
title: Computable bounds for MSO recognizing algebras
type: theorem
---
The effectivity argument starts with a syntax-computed bound for every
sort of an MSO recognizing algebra. Products multiply bounds, nonempty
powersets exponentiate them, and atomic path summaries have explicit
finite cardinalities.
-/

namespace Lax369799.QuantitativeRecognition
open RankedSystems Algebras SetLogic

def Bound (f : ℕ → ℕ) {A : RankedSet} (L : Language A) : Prop :=
  ∃ (B : RankedSet) (E : Algebra B) (η : RankedMap A B) (F : Set (B 0)),
    RankwiseFinite B ∧ Recognizes E η F L ∧ ∀ k,Nat.card (B k) ≤ f k

def logicBound {P : Type} : {X : Type} → Formula P X → ℕ → ℕ
  | _, .subset _ _, k => 2 ^ (4*(k+1))
  | _, .initial _, k => 2 ^ (4*(k+1))
  | _, .proposition _ _, k => 2 ^ (4*(k+1))
  | _, .edge _ _, k => 2 ^ (4*(k+1))
  | _, .neg φ, k => logicBound φ k
  | _, .disj φ ψ, k => logicBound φ k * logicBound ψ k
  | _, .existsSet φ, k => 2 ^ logicBound φ k

def msoBound {P : Type} (φ : MonadicSecondOrder.Sentence P) : ℕ → ℕ :=
  logicBound (SetLogicTranslation.translate φ (X := Empty) Fin.elim0 Fin.elim0)

axiom mso_bound {P : Type} [Finite P] (φ : MonadicSecondOrder.Sentence P) :
    Bound (msoBound φ) {S | MonadicSecondOrder.Models (TransitionEncoding.decode S) φ}

end Lax369799.QuantitativeRecognition