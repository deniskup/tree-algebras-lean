import Lax369799.MuSubstitution
import Mathlib.Data.Fin.Tuple.Basic

/-!
---
title: Scalar formulas for finite fixed-point equation systems
type: theorem
---
A simultaneous least or greatest solution of finitely many positive
modal equations is expressed by ordinary nested scalar fixed points.
Eliminate the tail equations with the head variable as a parameter,
solve the head equation, and substitute that solution in the tail.
-/
namespace Lax369799.FiniteMuEquations
open ModalMuCalculus TransitionSystems MuSubstitution

inductive Binder where | least | greatest

def bind {P : Type} {m : ℕ} : Binder → Formula P (m + 1) → Formula P m
  | .least, φ => .mu φ
  | .greatest, φ => .nu φ

def move (n m : ℕ) : Fin ((n + 1) + m) → Fin (n + (m + 1)) :=
  Fin.addCases (Fin.cases (Fin.natAdd n 0) (fun i => Fin.castAdd (m + 1) i))
    (fun j => Fin.natAdd n j.succ)

def headSubstitution {P : Type} {n m : ℕ} (g : Fin n → Formula P (m + 1)) :
    Fin ((n + 1) + m) → Formula P (m + 1) :=
  Fin.addCases (Fin.cases (.variable 0) g) (fun j => .variable j.succ)

def solve {P : Type} (b : Binder) : {n m : ℕ} → (Fin n → Formula P (n + m)) → Fin n → Formula P m
  | 0, _, _ => Fin.elim0
  | n + 1, m, φ =>
    let g := solve b (fun i : Fin n => rename (move n m) (φ i.succ))
    let a := bind b (substitute
      (Fin.addCases (Fin.cases (.variable 0) g) (fun j => .variable j.succ)) (φ 0))
    Fin.cases a (fun i => substitute (Fin.cases a Formula.variable) (g i))

def value {P : Type} (b : Binder) (S : TransitionSystem P) {n m : ℕ}
    (φ : Fin n → Formula P (n + m)) (ρ : Fin m → Set S.Vertex) : Fin n → Set S.Vertex :=
  match b with
  | .least => sInf {X | ∀ i, (φ i).eval S (Fin.addCases X ρ) ⊆ X i}
  | .greatest => sSup {X | ∀ i, X i ⊆ (φ i).eval S (Fin.addCases X ρ)}

axiom solve_correct {P : Type} (b : Binder) (S : TransitionSystem P) {n m : ℕ}
    (φ : Fin n → Formula P (n + m)) (ρ : Fin m → Set S.Vertex) :
    (fun i => (solve b φ i).eval S ρ) = value b S φ ρ

end Lax369799.FiniteMuEquations
