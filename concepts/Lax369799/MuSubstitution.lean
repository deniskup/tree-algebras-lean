import Lax369799.ModalMuCalculus

/-!
---
title: Substitution in modal fixed-point formulas
type: theorem
---
Renaming and simultaneous substitution preserve variable binding. Their
semantic laws allow finite systems of modal fixed-point equations to be
eliminated into the scalar syntax of the modal mu-calculus.
-/
namespace Lax369799.MuSubstitution
open ModalMuCalculus TransitionSystems

def lift {n m : ℕ} (f : Fin n → Fin m) : Fin (n + 1) → Fin (m + 1) :=
  Fin.cases 0 (fun i => (f i).succ)

def rename {P : Type} {n m : ℕ} (f : Fin n → Fin m) : Formula P n → Formula P m
  | .top => .top
  | .bot => .bot
  | .proposition p => .proposition p
  | .negProposition p => .negProposition p
  | .variable i => .variable (f i)
  | .conj φ ψ => .conj (rename f φ) (rename f ψ)
  | .disj φ ψ => .disj (rename f φ) (rename f ψ)
  | .diamond φ => .diamond (rename f φ)
  | .box φ => .box (rename f φ)
  | .mu φ => .mu (rename (lift f) φ)
  | .nu φ => .nu (rename (lift f) φ)

def liftSubstitution {P : Type} {n m : ℕ} (θ : Fin n → Formula P m) :
    Fin (n + 1) → Formula P (m + 1) :=
  Fin.cases (.variable 0) (fun i => rename Fin.succ (θ i))

def substitute {P : Type} {n m : ℕ} (θ : Fin n → Formula P m) : Formula P n → Formula P m
  | .top => .top
  | .bot => .bot
  | .proposition p => .proposition p
  | .negProposition p => .negProposition p
  | .variable i => θ i
  | .conj φ ψ => .conj (substitute θ φ) (substitute θ ψ)
  | .disj φ ψ => .disj (substitute θ φ) (substitute θ ψ)
  | .diamond φ => .diamond (substitute θ φ)
  | .box φ => .box (substitute θ φ)
  | .mu φ => .mu (substitute (liftSubstitution θ) φ)
  | .nu φ => .nu (substitute (liftSubstitution θ) φ)

axiom eval_rename {P : Type} (S : TransitionSystem P) {n m : ℕ}
    (φ : Formula P n) (f : Fin n → Fin m) (ρ : Fin m → Set S.Vertex) :
    (rename f φ).eval S ρ = φ.eval S (ρ ∘ f)

axiom eval_substitute {P : Type} (S : TransitionSystem P) {n m : ℕ}
    (φ : Formula P n) (θ : Fin n → Formula P m) (ρ : Fin m → Set S.Vertex) :
    (substitute θ φ).eval S ρ = φ.eval S (fun i => (θ i).eval S ρ)

end Lax369799.MuSubstitution
