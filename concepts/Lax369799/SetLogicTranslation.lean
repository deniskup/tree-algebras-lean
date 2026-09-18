import Lax369799.SetLogic

/-!
---
title: Translation to pure second-order logic
type: theorem
---
Vertex variables are represented by singleton-valued set variables. A
vertex quantifier becomes a set quantifier restricted to singletons; the
other atomic predicates have their usual singleton interpretations.
-/
namespace Lax369799.SetLogicTranslation
open TransitionSystems

def translate {P : Type} : {m n : ℕ} → MonadicSecondOrder.Formula P m n →
    {X : Type} → (Fin m → X) → (Fin n → X) → SetLogic.Formula P X
  | _, _, .equal x y, _, xv, _ => (SetLogic.Formula.subset (xv x) (xv y)).conj (.subset (xv y) (xv x))
  | _, _, .initial x, _, xv, _ => .initial (xv x)
  | _, _, .proposition p x, _, xv, _ => .proposition p (xv x)
  | _, _, .edge x y, _, xv, _ => .edge (xv x) (xv y)
  | _, _, .member x Y, _, xv, sv => .subset (xv x) (sv Y)
  | _, _, .neg φ, _, xv, sv => .neg (translate φ xv sv)
  | _, _, .disj φ ψ, _, xv, sv => .disj (translate φ xv sv) (translate ψ xv sv)
  | _, _, .existsVertex φ, _, xv, sv => .existsSet
      ((SetLogic.Formula.singleton .none).conj (translate φ (Fin.cases .none (fun i => .some (xv i))) (fun i => .some (sv i))))
  | _, _, .existsSet φ, _, xv, sv => .existsSet
      (translate φ (fun i => .some (xv i)) (Fin.cases .none (fun i => .some (sv i))))

axiom correct {P X : Type} {m n : ℕ} (S : TransitionSystem P)
    (φ : MonadicSecondOrder.Formula P m n) (xv : Fin m → X) (sv : Fin n → X)
    (σ : X → Set S.Vertex) (ρ : Fin m → S.Vertex) (τ : Fin n → Set S.Vertex)
    (hx : ∀ i, σ (xv i) = {ρ i}) (hs : ∀ i, σ (sv i) = τ i) :
    (translate φ xv sv).eval S σ ↔ φ.eval S ρ τ

end Lax369799.SetLogicTranslation
