import Lax369799.MuSubstitution

namespace Lax369799Proofs.MuSubstitution
open Lax369799
open ModalMuCalculus TransitionSystems MuSubstitution

private theorem lift_environment {n m : ℕ} {V : Type} (f : Fin n → Fin m)
    (ρ : Fin m → Set V) (X : Set V) :
    Fin.cases X ρ ∘ lift f = Fin.cases X (ρ ∘ f) := by
  funext i
  exact Fin.cases rfl (fun _ => rfl) i

/--
---
conclusion: Lax369799.MuSubstitution.eval_rename
---
Induction on syntax; under either binder, the newly bound variable is
fixed and the remaining environment is composed with the renaming.
-/
theorem eval_rename {P : Type} (S : TransitionSystem P) {n m : ℕ}
    (φ : Formula P n) (f : Fin n → Fin m) (ρ : Fin m → Set S.Vertex) :
    (rename f φ).eval S ρ = φ.eval S (ρ ∘ f) := by
  induction φ generalizing m with
  | top => rfl
  | bot => rfl
  | proposition p => rfl
  | negProposition p => rfl
  | «variable» i => rfl
  | conj φ ψ ihφ ihψ => simp only [rename, Formula.eval, ihφ, ihψ]
  | disj φ ψ ihφ ihψ => simp only [rename, Formula.eval, ihφ, ihψ]
  | diamond φ ih => simp only [rename, Formula.eval, ih]
  | box φ ih => simp only [rename, Formula.eval, ih]
  | mu φ ih => simp only [rename, Formula.eval, ih, lift_environment]
  | nu φ ih => simp only [rename, Formula.eval, ih, lift_environment]

private theorem substitution_environment {P : Type} (S : TransitionSystem P) {n m : ℕ}
    (θ : Fin n → Formula P m) (ρ : Fin m → Set S.Vertex) (X : Set S.Vertex) :
    (fun i => (liftSubstitution θ i).eval S (Fin.cases X ρ)) =
      Fin.cases X (fun i => (θ i).eval S ρ) := by
  funext i
  refine Fin.cases rfl (fun j => ?_) i
  exact eval_rename S (θ j) Fin.succ (Fin.cases X ρ)

/--
---
conclusion: Lax369799.MuSubstitution.eval_substitute
---
Substitute the denotations of the free variables. Shifting the substituted
formulas under a binder prevents capture by its new variable.
-/
theorem eval_substitute {P : Type} (S : TransitionSystem P) {n m : ℕ}
    (φ : Formula P n) (θ : Fin n → Formula P m) (ρ : Fin m → Set S.Vertex) :
    (substitute θ φ).eval S ρ = φ.eval S (fun i => (θ i).eval S ρ) := by
  induction φ generalizing m with
  | top => rfl
  | bot => rfl
  | proposition p => rfl
  | negProposition p => rfl
  | «variable» i => rfl
  | conj φ ψ ihφ ihψ => simp only [substitute, Formula.eval, ihφ, ihψ]
  | disj φ ψ ihφ ihψ => simp only [substitute, Formula.eval, ihφ, ihψ]
  | diamond φ ih => simp only [substitute, Formula.eval, ih]
  | box φ ih => simp only [substitute, Formula.eval, ih]
  | mu φ ih => simp only [substitute, Formula.eval, ih, substitution_environment]
  | nu φ ih => simp only [substitute, Formula.eval, ih, substitution_environment]

end Lax369799Proofs.MuSubstitution
