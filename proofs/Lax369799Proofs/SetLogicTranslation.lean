import Lax369799.SetLogicTranslation
import Lax369799Proofs.SetLogic

namespace Lax369799Proofs.SetLogicTranslation
open Lax369799.TransitionSystems Lax369799.SetLogicTranslation
open Lax369799Proofs.SetLogic

/--
---
conclusion: Lax369799.SetLogicTranslation.correct
---
Induction on the first-order and set-variable syntax. Singleton sets give
exactly the choices for an existential vertex quantifier.
-/
theorem correct {P X : Type} {m n : ℕ} (S : TransitionSystem P)
    (φ : Lax369799.MonadicSecondOrder.Formula P m n) (xv : Fin m → X) (sv : Fin n → X)
    (σ : X → Set S.Vertex) (ρ : Fin m → S.Vertex) (τ : Fin n → Set S.Vertex)
    (hx : ∀ i, σ (xv i) = {ρ i}) (hs : ∀ i, σ (sv i) = τ i) :
    (translate φ xv sv).eval S σ ↔ φ.eval S ρ τ := by
  induction φ generalizing X with
  | equal x y => simp [translate, eval_conj, Lax369799.SetLogic.Formula.eval, Lax369799.MonadicSecondOrder.Formula.eval, hx, Set.subset_def, eq_comm]
  | initial x => simp [translate, Lax369799.SetLogic.Formula.eval, Lax369799.MonadicSecondOrder.Formula.eval, hx, eq_comm]
  | proposition p x => simp [translate, Lax369799.SetLogic.Formula.eval, Lax369799.MonadicSecondOrder.Formula.eval, hx]
  | edge x y => simp [translate, Lax369799.SetLogic.Formula.eval, Lax369799.MonadicSecondOrder.Formula.eval, hx]
  | member x Y => simp [translate, Lax369799.SetLogic.Formula.eval, Lax369799.MonadicSecondOrder.Formula.eval, hx, hs]
  | neg φ ih => exact not_congr (ih xv sv σ ρ τ hx hs)
  | disj φ ψ ihφ ihψ => exact or_congr (ihφ xv sv σ ρ τ hx hs) (ihψ xv sv σ ρ τ hx hs)
  | existsVertex φ ih =>
    simp only [translate, Lax369799.SetLogic.Formula.eval, eval_conj, singleton_iff, Lax369799.MonadicSecondOrder.Formula.eval, Option.elim_none]
    constructor
    · rintro ⟨U, ⟨v, rfl⟩, h⟩
      refine ⟨v, (ih _ _ _ (Fin.cases v ρ) τ ?_ ?_).mp h⟩
      · intro i
        refine Fin.cases ?_ (fun j => ?_) i
        · rfl
        · exact hx j
      · exact hs
    · rintro ⟨v, h⟩
      refine ⟨{v}, ⟨v, rfl⟩, (ih _ _ _ (Fin.cases v ρ) τ ?_ ?_).mpr h⟩
      · intro i
        refine Fin.cases ?_ (fun j => ?_) i
        · rfl
        · exact hx j
      · exact hs
  | existsSet φ ih =>
    simp only [translate, Lax369799.SetLogic.Formula.eval, Lax369799.MonadicSecondOrder.Formula.eval]
    apply exists_congr
    intro U
    apply ih _ _ _ ρ (Fin.cases U τ)
    · exact hx
    · intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · rfl
      · exact hs j

end Lax369799Proofs.SetLogicTranslation
