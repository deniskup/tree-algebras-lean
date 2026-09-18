import Lax369799.MonadicSecondOrder

/-!
---
title: Pure second-order syntax
type: theorem
---
The set-only presentation of MSO uses inclusion, initial membership,
universal proposition tests, and existential edge tests. Bound variables
are represented by a new option value. Empty sets and singletons are
definable using inclusion and quantification over sets, as in Section 6.2.
-/
namespace Lax369799.SetLogic
open TransitionSystems

inductive Formula (P : Type) : Type → Type 1
  | subset {X} : X → X → Formula P X
  | initial {X} : X → Formula P X
  | proposition {X} : P → X → Formula P X
  | edge {X} : X → X → Formula P X
  | neg {X} : Formula P X → Formula P X
  | disj {X} : Formula P X → Formula P X → Formula P X
  | existsSet {X} : Formula P (Option X) → Formula P X

def Formula.eval {P : Type} (S : TransitionSystem P) :
    {X : Type} → Formula P X → (X → Set S.Vertex) → Prop
  | _, .subset x y, σ => σ x ⊆ σ y
  | _, .initial x, σ => S.initial ∈ σ x
  | _, .proposition p x, σ => ∀ v ∈ σ x, p ∈ S.valuation v
  | _, .edge x y, σ => ∃ v ∈ σ x, ∃ w ∈ σ y, S.edge v w
  | _, .neg φ, σ => ¬ φ.eval S σ
  | _, .disj φ ψ, σ => φ.eval S σ ∨ ψ.eval S σ
  | _, .existsSet φ, σ => ∃ U, φ.eval S (Option.elim · U σ)

def Formula.conj {P X : Type} (φ ψ : Formula P X) : Formula P X :=
  .neg (.disj (.neg φ) (.neg ψ))

def Formula.empty {P X : Type} (x : X) : Formula P X :=
  .neg (.existsSet (.neg (.subset (.some x) .none)))

def Formula.singleton {P X : Type} (x : X) : Formula P X :=
  .conj (.neg (.empty x)) (.neg (.existsSet
    (.conj (.subset .none (.some x))
      (.conj (.neg (.empty .none)) (.neg (.subset (.some x) .none))))))

axiom empty_iff {P X : Type} (S : TransitionSystem P) (σ : X → Set S.Vertex) (x : X) :
    (Formula.empty x).eval S σ ↔ σ x = ∅

axiom singleton_iff {P X : Type} (S : TransitionSystem P) (σ : X → Set S.Vertex) (x : X) :
    (Formula.singleton x).eval S σ ↔ ∃ v, σ x = {v}

end Lax369799.SetLogic
