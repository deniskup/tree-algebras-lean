import Lax369799.FiniteModelChecking
import Lax369799Proofs.UnrestrictedLogic
import Mathlib.Data.Fintype.Pi

set_option backward.isDefEq.respectTransparency false
namespace Lax369799Proofs.FiniteModelChecking
open Lax369799
open Lax369799.FiniteModelChecking

private theorem bool_cases {V : Type} {n : ℕ} (X : V → Bool) (ρ : Fin n → V → Bool) :
    (fun i => {v | Fin.cases X ρ i v = true}) = Fin.cases {v | X v = true} (fun i => {v | ρ i v = true}) := by
  funext i
  exact Fin.cases rfl (fun _ => rfl) i

private theorem set_encode {V : Type} (X : Set V) :
    ∃ Y : V → Bool,{v | Y v = true} = X := by
  classical
  exact ⟨fun v => decide (v ∈ X),by ext v;exact decide_eq_true_iff⟩

/--
---
conclusion: Lax369799.FiniteModelChecking.mso_correct
---
Finite Boolean quantification agrees with quantification over vertices
and arbitrary vertex subsets.
-/
theorem mso_correct {P : Type} {k m n : ℕ} (G : Graph P k)
    (φ : MonadicSecondOrder.Formula P m n) (ρ : Fin m → Fin (k+1))
    (σ : Fin n → Fin (k+1) → Bool) :
    msoCheck G φ ρ σ = true ↔ UnrestrictedLogic.msoEval (semantics G) φ ρ (fun i => {v | σ i v = true}) := by
  induction φ with
  | equal x y => exact decide_eq_true_iff
  | initial x => exact decide_eq_true_iff
  | proposition p x => rfl
  | edge x y => rfl
  | member x X => rfl
  | neg φ ih =>
    have hh := ih ρ σ
    cases hb : msoCheck G φ ρ σ <;> simp_all [msoCheck,UnrestrictedLogic.msoEval]
  | disj φ ψ ihφ ihψ => simpa only [msoCheck,Bool.or_eq_true,UnrestrictedLogic.msoEval] using or_congr (ihφ ρ σ) (ihψ ρ σ)
  | existsVertex φ ih =>
    simp only [msoCheck,decide_eq_true_eq,UnrestrictedLogic.msoEval]
    exact exists_congr (fun v => ih (Fin.cases v ρ) σ)
  | existsSet φ ih =>
    simp only [msoCheck,decide_eq_true_eq,UnrestrictedLogic.msoEval]
    constructor
    · rintro ⟨X,h⟩
      have hh := (ih ρ (Fin.cases X σ)).mp h
      rw [bool_cases] at hh
      exact ⟨_,hh⟩
    · rintro ⟨X,h⟩
      obtain ⟨Y,hy⟩ := set_encode X
      refine ⟨Y,(ih ρ (Fin.cases Y σ)).mpr ?_⟩
      rw [bool_cases,hy]; exact h

/--
---
conclusion: Lax369799.FiniteModelChecking.mu_correct
---
Finite Boolean quantification agrees with quantification over vertices
and arbitrary vertex subsets.
-/
theorem mu_correct {P : Type} {k n : ℕ} (G : Graph P k)
    (φ : ModalMuCalculus.Formula P n) (ρ : Fin n → Fin (k+1) → Bool) (v : Fin (k+1)) :
    muCheck G φ ρ v = true ↔ v ∈ UnrestrictedLogic.muEval (semantics G) φ (fun i => {w | ρ i w = true}) := by
  induction φ generalizing v with
  | top => simp [muCheck,UnrestrictedLogic.muEval]
  | bot => simp [muCheck,UnrestrictedLogic.muEval]
  | proposition p => exact Iff.rfl
  | negProposition p => simp [muCheck,UnrestrictedLogic.muEval,semantics]
  | «variable» i => exact Iff.rfl
  | conj φ ψ ihφ ihψ => simpa only [muCheck,Bool.and_eq_true,UnrestrictedLogic.muEval,Set.mem_inter_iff] using and_congr (ihφ ρ v) (ihψ ρ v)
  | disj φ ψ ihφ ihψ => simpa only [muCheck,Bool.or_eq_true,UnrestrictedLogic.muEval,Set.mem_union] using or_congr (ihφ ρ v) (ihψ ρ v)
  | diamond φ ih =>
    simp only [muCheck,decide_eq_true_eq,UnrestrictedLogic.muEval,Set.mem_ofPred_eq,semantics]
    exact exists_congr (fun w => and_congr Iff.rfl (ih ρ w))
  | box φ ih =>
    simp only [muCheck,decide_eq_true_eq,UnrestrictedLogic.muEval,Set.mem_ofPred_eq,semantics]
    exact forall_congr' (fun w => imp_congr_right (fun _ => ih ρ w))
  | mu φ ih =>
    simp only [muCheck,decide_eq_true_eq,UnrestrictedLogic.muEval]
    constructor
    · intro h X hx
      obtain ⟨Y,hy⟩ := set_encode X
      have ha := h Y (by
        intro w hw
        have hh := (ih (Fin.cases Y ρ) w).mp hw
        rw [bool_cases,hy] at hh
        change w ∈ {v | Y v = true}
        rw [hy]
        exact hx hh)
      change v ∈ X
      rw [← hy]
      exact ha
    · intro h X hx
      apply h {w | X w = true}
      intro w hw
      have hh : muCheck G φ (Fin.cases X ρ) w = true := by
        apply (ih (Fin.cases X ρ) w).mpr
        rw [bool_cases]; exact hw
      exact hx w hh
  | nu φ ih =>
    simp only [muCheck,decide_eq_true_eq,UnrestrictedLogic.muEval]
    constructor
    · rintro ⟨X,hv,hx⟩
      refine ⟨{w | X w = true},?_,hv⟩
      intro w hw
      have hh := (ih (Fin.cases X ρ) w).mp (hx w hw)
      rw [bool_cases] at hh
      exact hh
    · rintro ⟨X,hx,hv⟩
      obtain ⟨Y,hy⟩ := set_encode X
      refine ⟨Y,by change v ∈ {w | Y w = true};rw [hy];exact hv,?_⟩
      intro w hw
      apply (ih (Fin.cases Y ρ) w).mpr
      rw [bool_cases,hy]
      apply hx
      rw [← hy]
      exact hw

end Lax369799Proofs.FiniteModelChecking
