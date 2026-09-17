import Lax369799.TransitionSystems

/-!
---
title: Monadic second-order logic on transition systems
type: definition
---
MSO has vertex variables, set variables, equality, the initial-vertex
predicate, proposition predicates, the edge relation, membership, Boolean
connectives, and quantification over vertices and arbitrary vertex sets.
The two natural-number indices count the free variables of each kind;
a sentence has no free variables. Semantics is given by the usual Tarski
clauses (Section 6.2).
-/

namespace Lax369799.MonadicSecondOrder
open TransitionSystems

inductive Formula (P : Type) : ℕ → ℕ → Type
  | equal {m n} : Fin m → Fin m → Formula P m n
  | initial {m n} : Fin m → Formula P m n
  | proposition {m n} : P → Fin m → Formula P m n
  | edge {m n} : Fin m → Fin m → Formula P m n
  | member {m n} : Fin m → Fin n → Formula P m n
  | neg {m n} : Formula P m n → Formula P m n
  | disj {m n} : Formula P m n → Formula P m n → Formula P m n
  | existsVertex {m n} : Formula P (m + 1) n → Formula P m n
  | existsSet {m n} : Formula P m (n + 1) → Formula P m n

def Formula.eval {P : Type} (S : TransitionSystem P) :
    {m n : ℕ} → Formula P m n → (Fin m → S.Vertex) →
    (Fin n → Set S.Vertex) → Prop
  | _, _, .equal x y, ρ, _ => ρ x = ρ y
  | _, _, .initial x, ρ, _ => ρ x = S.initial
  | _, _, .proposition p x, ρ, _ => p ∈ S.valuation (ρ x)
  | _, _, .edge x y, ρ, _ => S.edge (ρ x) (ρ y)
  | _, _, .member x X, ρ, σ => ρ x ∈ σ X
  | _, _, .neg φ, ρ, σ => ¬ φ.eval S ρ σ
  | _, _, .disj φ ψ, ρ, σ => φ.eval S ρ σ ∨ ψ.eval S ρ σ
  | _, _, .existsVertex φ, ρ, σ => ∃ v, φ.eval S (Fin.cases v ρ) σ
  | _, _, .existsSet φ, ρ, σ => ∃ X, φ.eval S ρ (Fin.cases X σ)

abbrev Sentence (P : Type) := Formula P 0 0

def Models {P : Type} (S : TransitionSystem P) (φ : Sentence P) : Prop :=
  φ.eval S Fin.elim0 Fin.elim0

def Definable {P : Type} (L : Set (TransitionSystem P)) : Prop :=
  ∃ φ : Sentence P, ∀ S, S ∈ L ↔ Models S φ

end Lax369799.MonadicSecondOrder
