import Lax369799.UnrestrictedLogic
import Mathlib.Data.Fintype.Pi

/-!
---
title: Executable finite model checking for both logics
type: theorem
---
Finite graphs and set assignments are Boolean tables. Quantifiers range
over explicitly finite types, including all Boolean set assignments.
The fixed-point clauses test every pre-fixed or post-fixed subset.
-/

namespace Lax369799.FiniteModelChecking

abbrev Graph (P : Type) (k : ℕ) :=
  Fin (k+1) × (Fin (k+1) → Fin (k+1) → Bool) × (Fin (k+1) → P → Bool)

def semantics {P : Type} {k : ℕ} (G : Graph P k) : UnrestrictedTransitionSystems.TransitionSystem P :=
  ⟨Fin (k+1),G.1,(fun v w => G.2.1 v w = true),(fun v => {p | G.2.2 v p = true})⟩

def msoCheck {P : Type} {k : ℕ} (G : Graph P k) :
    {m n : ℕ} → MonadicSecondOrder.Formula P m n → (Fin m → Fin (k+1)) →
      (Fin n → Fin (k+1) → Bool) → Bool
  | _, _, .equal x y, ρ, _ => decide (ρ x = ρ y)
  | _, _, .initial x, ρ, _ => decide (ρ x = G.1)
  | _, _, .proposition p x, ρ, _ => G.2.2 (ρ x) p
  | _, _, .edge x y, ρ, _ => G.2.1 (ρ x) (ρ y)
  | _, _, .member x X, ρ, σ => σ X (ρ x)
  | _, _, .neg φ, ρ, σ => !(msoCheck G φ ρ σ)
  | _, _, .disj φ ψ, ρ, σ => msoCheck G φ ρ σ || msoCheck G ψ ρ σ
  | _, _, .existsVertex φ, ρ, σ => decide (∃ v,msoCheck G φ (Fin.cases v ρ) σ = true)
  | _, _, .existsSet φ, ρ, σ => decide (∃ X : Fin (k+1) → Bool,msoCheck G φ ρ (Fin.cases X σ) = true)

def muCheck {P : Type} {k : ℕ} (G : Graph P k) :
    {n : ℕ} → ModalMuCalculus.Formula P n → (Fin n → Fin (k+1) → Bool) → Fin (k+1) → Bool
  | _, .top, _, _ => true
  | _, .bot, _, _ => false
  | _, .proposition p, _, v => G.2.2 v p
  | _, .negProposition p, _, v => !(G.2.2 v p)
  | _, .variable i, ρ, v => ρ i v
  | _, .conj φ ψ, ρ, v => muCheck G φ ρ v && muCheck G ψ ρ v
  | _, .disj φ ψ, ρ, v => muCheck G φ ρ v || muCheck G ψ ρ v
  | _, .diamond φ, ρ, v => decide (∃ w,G.2.1 v w = true ∧ muCheck G φ ρ w = true)
  | _, .box φ, ρ, v => decide (∀ w,G.2.1 v w = true → muCheck G φ ρ w = true)
  | _, .mu φ, ρ, v => decide (∀ X : Fin (k+1) → Bool,
      (∀ w,muCheck G φ (Fin.cases X ρ) w = true → X w = true) → X v = true)
  | _, .nu φ, ρ, v => decide (∃ X : Fin (k+1) → Bool,
      X v = true ∧ ∀ w,X w = true → muCheck G φ (Fin.cases X ρ) w = true)

def mso {P : Type} {k : ℕ} (G : Graph P k) (φ : MonadicSecondOrder.Sentence P) : Bool :=
  msoCheck G φ Fin.elim0 Fin.elim0

def mu {P : Type} {k : ℕ} (G : Graph P k) (φ : ModalMuCalculus.Sentence P) : Bool :=
  muCheck G φ Fin.elim0 G.1

axiom mso_correct {P : Type} {k m n : ℕ} (G : Graph P k)
    (φ : MonadicSecondOrder.Formula P m n) (ρ : Fin m → Fin (k+1))
    (σ : Fin n → Fin (k+1) → Bool) :
    msoCheck G φ ρ σ = true ↔ UnrestrictedLogic.msoEval (semantics G) φ ρ (fun i => {v | σ i v = true})

axiom mu_correct {P : Type} {k n : ℕ} (G : Graph P k)
    (φ : ModalMuCalculus.Formula P n) (ρ : Fin n → Fin (k+1) → Bool) (v : Fin (k+1)) :
    muCheck G φ ρ v = true ↔ v ∈ UnrestrictedLogic.muEval (semantics G) φ (fun i => {w | ρ i w = true})

end Lax369799.FiniteModelChecking