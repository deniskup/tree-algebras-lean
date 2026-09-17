import Lax369799.TransitionSystems
import Mathlib.Order.CompleteLattice.Basic

/-!
---
title: Modal mu-calculus
type: definition
---
The modal mu-calculus is presented in negation normal form: negation is
allowed on proposition letters, and all fixed-point variables occur
positively. Formulas have conjunction, disjunction, box, diamond, and least
and greatest fixed points. A binder introduces variable zero and shifts
the previous free variables. Least fixed points are intersections of
pre-fixed points; greatest fixed points are unions of post-fixed points.
A closed formula is evaluated at the initial vertex.
-/

namespace Lax369799.ModalMuCalculus
open TransitionSystems

inductive Formula (P : Type) : ℕ → Type
  | top {n} : Formula P n
  | bot {n} : Formula P n
  | proposition {n} : P → Formula P n
  | negProposition {n} : P → Formula P n
  | variable {n} : Fin n → Formula P n
  | conj {n} : Formula P n → Formula P n → Formula P n
  | disj {n} : Formula P n → Formula P n → Formula P n
  | diamond {n} : Formula P n → Formula P n
  | box {n} : Formula P n → Formula P n
  | mu {n} : Formula P (n + 1) → Formula P n
  | nu {n} : Formula P (n + 1) → Formula P n

def Formula.eval {P : Type} (S : TransitionSystem P) :
    {n : ℕ} → Formula P n → (Fin n → Set S.Vertex) → Set S.Vertex
  | _, .top, _ => Set.univ
  | _, .bot, _ => ∅
  | _, .proposition p, _ => {v | p ∈ S.valuation v}
  | _, .negProposition p, _ => {v | p ∉ S.valuation v}
  | _, .variable x, ρ => ρ x
  | _, .conj φ ψ, ρ => φ.eval S ρ ∩ ψ.eval S ρ
  | _, .disj φ ψ, ρ => φ.eval S ρ ∪ ψ.eval S ρ
  | _, .diamond φ, ρ => {v | ∃ w, S.edge v w ∧ w ∈ φ.eval S ρ}
  | _, .box φ, ρ => {v | ∀ w, S.edge v w → w ∈ φ.eval S ρ}
  | _, .mu φ, ρ => sInf {X | φ.eval S (Fin.cases X ρ) ⊆ X}
  | _, .nu φ, ρ => sSup {X | X ⊆ φ.eval S (Fin.cases X ρ)}

abbrev Sentence (P : Type) := Formula P 0

def Models {P : Type} (S : TransitionSystem P) (φ : Sentence P) : Prop :=
  S.initial ∈ φ.eval S Fin.elim0

def Definable {P : Type} (L : Set (TransitionSystem P)) : Prop :=
  ∃ φ : Sentence P, ∀ S, S ∈ L ↔ Models S φ

end Lax369799.ModalMuCalculus
