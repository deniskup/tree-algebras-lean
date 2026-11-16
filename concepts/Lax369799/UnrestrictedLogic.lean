import Lax369799.UnrestrictedTransitionSystems
import Lax369799.MonadicSecondOrder
import Lax369799.ModalMuCalculus
import Mathlib.Order.FixedPoints
import Mathlib.Data.Set.Lattice

/-!
---
title: Logic on arbitrary transition systems
type: theorem
---
Transition systems may have arbitrary state spaces. The usual MSO and
modal fixed-point semantics agree with the finite-system semantics on
finite presentations. The modal mu-calculus translates to MSO and is
bisimulation invariant on arbitrary state spaces.
-/

namespace Lax369799.UnrestrictedLogic
open UnrestrictedTransitionSystems

def muEval {P : Type} (S : TransitionSystem P) :
    {n : ℕ} → ModalMuCalculus.Formula P n → (Fin n → Set S.Vertex) → Set S.Vertex
  | _, .top, _ => Set.univ
  | _, .bot, _ => ∅
  | _, .proposition p, _ => {v | p ∈ S.valuation v}
  | _, .negProposition p, _ => {v | p ∉ S.valuation v}
  | _, .variable i, ρ => ρ i
  | _, .conj φ ψ, ρ => muEval S φ ρ ∩ muEval S ψ ρ
  | _, .disj φ ψ, ρ => muEval S φ ρ ∪ muEval S ψ ρ
  | _, .diamond φ, ρ => {v | ∃ w, S.edge v w ∧ w ∈ muEval S φ ρ}
  | _, .box φ, ρ => {v | ∀ w, S.edge v w → w ∈ muEval S φ ρ}
  | _, .mu φ, ρ => sInf {X | muEval S φ (Fin.cases X ρ) ⊆ X}
  | _, .nu φ, ρ => sSup {X | X ⊆ muEval S φ (Fin.cases X ρ)}

def msoEval {P : Type} (S : TransitionSystem P) :
    {m n : ℕ} → MonadicSecondOrder.Formula P m n → (Fin m → S.Vertex) →
      (Fin n → Set S.Vertex) → Prop
  | _, _, .equal x y, ρ, _ => ρ x = ρ y
  | _, _, .initial x, ρ, _ => ρ x = S.initial
  | _, _, .proposition p x, ρ, _ => p ∈ S.valuation (ρ x)
  | _, _, .edge x y, ρ, _ => S.edge (ρ x) (ρ y)
  | _, _, .member x X, ρ, σ => ρ x ∈ σ X
  | _, _, .neg φ, ρ, σ => ¬ msoEval S φ ρ σ
  | _, _, .disj φ ψ, ρ, σ => msoEval S φ ρ σ ∨ msoEval S ψ ρ σ
  | _, _, .existsVertex φ, ρ, σ => ∃ v, msoEval S φ (Fin.cases v ρ) σ
  | _, _, .existsSet φ, ρ, σ => ∃ X, msoEval S φ ρ (Fin.cases X σ)

def MuModels {P : Type} (S : TransitionSystem P) (φ : ModalMuCalculus.Sentence P) : Prop :=
  S.initial ∈ muEval S φ Fin.elim0

def MSOModels {P : Type} (S : TransitionSystem P) (φ : MonadicSecondOrder.Sentence P) : Prop :=
  msoEval S φ Fin.elim0 Fin.elim0

def MuDefinable {P : Type} (L : Set (TransitionSystem P)) : Prop :=
  ∃ φ : ModalMuCalculus.Sentence P, ∀ S, S ∈ L ↔ MuModels S φ

def MSODefinable {P : Type} (L : Set (TransitionSystem P)) : Prop :=
  ∃ φ : MonadicSecondOrder.Sentence P, ∀ S, S ∈ L ↔ MSOModels S φ

def conjunction {P : Type} {m n : ℕ}
    (φ ψ : MonadicSecondOrder.Formula P m n) : MonadicSecondOrder.Formula P m n :=
  .neg (.disj (.neg φ) (.neg ψ))

def implication {P : Type} {m n : ℕ}
    (φ ψ : MonadicSecondOrder.Formula P m n) : MonadicSecondOrder.Formula P m n :=
  .disj (.neg φ) ψ

def allVertex {P : Type} {m n : ℕ}
    (φ : MonadicSecondOrder.Formula P (m + 1) n) : MonadicSecondOrder.Formula P m n :=
  .neg (.existsVertex (.neg φ))

def allSet {P : Type} {m n : ℕ}
    (φ : MonadicSecondOrder.Formula P m (n + 1)) : MonadicSecondOrder.Formula P m n :=
  .neg (.existsSet (.neg φ))

/-- Translate satisfaction at a designated first-order variable. -/
def translate {P : Type} : {n : ℕ} → ModalMuCalculus.Formula P n →
    {m : ℕ} → Fin m → MonadicSecondOrder.Formula P m n
  | _, .top, _, x => .equal x x
  | _, .bot, _, x => .neg (.equal x x)
  | _, .proposition p, _, x => .proposition p x
  | _, .negProposition p, _, x => .neg (.proposition p x)
  | _, .variable i, _, x => .member x i
  | _, .conj φ ψ, _, x => conjunction (translate φ x) (translate ψ x)
  | _, .disj φ ψ, _, x => .disj (translate φ x) (translate ψ x)
  | _, .diamond φ, _, x => .existsVertex (conjunction (.edge x.succ 0) (translate φ 0))
  | _, .box φ, _, x => allVertex (implication (.edge x.succ 0) (translate φ 0))
  | _, .mu φ, _, x => allSet (implication
      (allVertex (implication (translate φ 0) (.member 0 0))) (.member x 0))
  | _, .nu φ, _, x => .existsSet (conjunction (.member x 0)
      (allVertex (implication (.member 0 0) (translate φ 0))))

def sentence {P : Type} (φ : ModalMuCalculus.Sentence P) : MonadicSecondOrder.Sentence P :=
  .existsVertex (conjunction (.initial 0) (translate φ 0))

axiom finite_mu {P : Type} (S : TransitionSystems.TransitionSystem P) {n : ℕ}
    (φ : ModalMuCalculus.Formula P n) (ρ : Fin n → Set S.Vertex) :
    muEval (ofFinite S) φ ρ = φ.eval S ρ

axiom finite_mso {P : Type} (S : TransitionSystems.TransitionSystem P) {m n : ℕ}
    (φ : MonadicSecondOrder.Formula P m n) (ρ : Fin m → S.Vertex) (σ : Fin n → Set S.Vertex) :
    msoEval (ofFinite S) φ ρ σ ↔ φ.eval S ρ σ

axiom eval_monotone {P : Type} (S : TransitionSystem P) {n : ℕ}
    (φ : ModalMuCalculus.Formula P n) (ρ σ : Fin n → Set S.Vertex)
    (h : ∀ i, ρ i ⊆ σ i) : muEval S φ ρ ⊆ muEval S φ σ

axiom translate_correct {P : Type} (S : TransitionSystem P) {n : ℕ}
    (φ : ModalMuCalculus.Formula P n) {m : ℕ} (x : Fin m)
    (ρ : Fin m → S.Vertex) (σ : Fin n → Set S.Vertex) :
    msoEval S (translate φ x) ρ σ ↔ ρ x ∈ muEval S φ σ

axiom mu_to_mso {P : Type} (φ : ModalMuCalculus.Sentence P) :
    ∃ ψ : MonadicSecondOrder.Sentence P, ∀ S : TransitionSystem P,
      MuModels S φ ↔ MSOModels S ψ

axiom mu_bisimulation_invariant {P : Type} (φ : ModalMuCalculus.Sentence P) :
    BisimulationInvariant {S | MuModels S φ}

axiom mu_definable_implies_mso_invariant {P : Type} (L : Set (TransitionSystem P))
    (hL : MuDefinable L) : MSODefinable L ∧ BisimulationInvariant L

axiom finite_bisimulation {P : Type} (S T : TransitionSystems.TransitionSystem P)
    (R : S.Vertex → T.Vertex → Prop) :
    Bisimulation (ofFinite S) (ofFinite T) R ↔ TransitionSystems.Bisimulation S T R

axiom finite_mu_models {P : Type} (S : TransitionSystems.TransitionSystem P)
    (φ : ModalMuCalculus.Sentence P) : MuModels (ofFinite S) φ ↔ ModalMuCalculus.Models S φ

axiom finite_mso_models {P : Type} (S : TransitionSystems.TransitionSystem P)
    (φ : MonadicSecondOrder.Sentence P) : MSOModels (ofFinite S) φ ↔ MonadicSecondOrder.Models S φ

end Lax369799.UnrestrictedLogic

