import Lax369799.FiniteTesting
import Lax369799.FiniteModalData
import Lax369799Proofs.FiniteModelChecking
import Lax369799Proofs.FiniteModalData

set_option backward.isDefEq.respectTransparency false
namespace Lax369799Proofs.FiniteTesting
open Lax369799
open TransitionSystems FiniteModelChecking
open Lax369799.FiniteTesting

private theorem valid_iff {P : Type} {k : ℕ} (G : Graph P k) :
    valid G = true ↔ ∀ v,Relation.ReflTransGen (semantics G).edge G.1 v := by
  classical
  simp only [valid,decide_eq_true_eq]
  constructor
  · intro h v
    let X : Fin (k+1) → Bool := fun w => decide (Relation.ReflTransGen (semantics G).edge G.1 w)
    have hx : X G.1 = true := by simp only [X,decide_eq_true_eq];exact .refl
    have hc : ∀ v w,X v = true → G.2.1 v w = true → X w = true := by
      intro v w hv hw
      simp only [X,decide_eq_true_eq] at hv ⊢
      exact hv.tail hw
    exact of_decide_eq_true (h X hx hc v)
  · intro h X hx hc v
    have hp := h v
    induction hp with
    | refl => exact hx
    | @tail v w hp he ih => exact hc v w ih he

private theorem check_reflection {P : Type} {k : ℕ} (G : Graph P k)
    (S : TransitionSystem P) (he : semantics G = UnrestrictedTransitionSystems.ofFinite S)
    (φ : MonadicSecondOrder.Sentence P) (ψ : ModalMuCalculus.Sentence P) :
    (mso G φ = true ↔ MonadicSecondOrder.Models S φ) ∧
    (mu G ψ = true ↔ ModalMuCalculus.Models S ψ) := by
  have hm := FiniteModelChecking.mso_correct G φ Fin.elim0 Fin.elim0
  have hn := FiniteModelChecking.mu_correct G ψ Fin.elim0 G.1
  have hem : (fun i : Fin 0 => {v : Fin (k+1) | (Fin.elim0 i : Fin (k+1) → Bool) v = true}) = Fin.elim0 :=
    funext (fun i => Fin.elim0 i)
  have hm' : mso G φ = true ↔ UnrestrictedLogic.MSOModels (semantics G) φ :=
    hm.trans (Iff.of_eq (congrArg (fun env => UnrestrictedLogic.msoEval (semantics G) φ Fin.elim0 env) hem))
  have hn' : mu G ψ = true ↔ UnrestrictedLogic.MuModels (semantics G) ψ :=
    hn.trans (Iff.of_eq (congrArg (fun env => G.1 ∈ UnrestrictedLogic.muEval (semantics G) ψ env) hem))
  rw [he] at hm' hn'
  exact ⟨hm'.trans (UnrestrictedLogic.finite_mso_models S φ),hn'.trans (UnrestrictedLogic.finite_mu_models S ψ)⟩

/--
---
conclusion: Lax369799.FiniteTesting.test_correct
---
The closure-set test detects exactly the reachable graph codes. Complete
finite table enumeration and the two verified model checkers identify
the Boolean test with agreement on all finite systems within the bound.
-/
theorem test_correct {P : Type} [Fintype P] [Encodable P] [DecidableEq P] (K : ℕ)
    (φ : MonadicSecondOrder.Sentence P) (ψ : ModalMuCalculus.Sentence P) :
    test K φ ψ = true ↔ ∀ S : TransitionSystem P,S.size ≤ K →
      (MonadicSecondOrder.Models S φ ↔ ModalMuCalculus.Models S ψ) := by
  classical
  simp only [test,List.all_eq_true]
  constructor
  · intro h S hs
    rcases S with ⟨s,init,edge,valuation,reachable⟩
    cases s with
    | zero => exact Fin.elim0 init
    | succ k =>
      let S : TransitionSystem P := ⟨k+1,init,edge,valuation,reachable⟩
      let G : Graph P k := ⟨init,(fun v w => decide (edge v w)),fun v p => decide (p ∈ valuation v)⟩
      have hedge : (fun v w => decide (edge v w) = true) = edge := by
        funext v w;exact propext decide_eq_true_iff
      have hval : (fun v => {p | decide (p ∈ valuation v) = true}) = valuation := by
        funext v;ext p;exact decide_eq_true_iff
      have he : semantics G = UnrestrictedTransitionSystems.ofFinite S := by
        change (⟨Fin (k+1),init,_,_⟩ : UnrestrictedTransitionSystems.TransitionSystem P) = _
        rw [hedge,hval]
        rfl
      have hv : valid G = true := by
        apply (valid_iff G).mpr
        change ∀ v,Relation.ReflTransGen (fun v w => decide (edge v w) = true) init v
        rw [hedge]
        exact reachable
      have hh := h k (List.mem_range.mpr (by change k+1 ≤ K at hs;omega)) G
        (FiniteModalData.mem_elements _ G)
      have hh' : mso G φ = mu G ψ := by simpa only [agree,hv,↓reduceIte,beq_iff_eq] using hh
      obtain ⟨hm,hn⟩ := check_reflection G S he φ ψ
      exact hm.symm.trans ((Iff.of_eq (congrArg (· = true) hh')).trans hn)
  · intro h k hk G hG
    by_cases hv : valid G = true
    · let S : TransitionSystem P := ⟨k+1,G.1,(semantics G).edge,(semantics G).valuation,(valid_iff G).mp hv⟩
      have he : semantics G = UnrestrictedTransitionSystems.ofFinite S := rfl
      obtain ⟨hm,hn⟩ := check_reflection G S he φ ψ
      have hh := hm.trans ((h S (by have := List.mem_range.mp hk;change k+1 ≤ K;omega)).trans hn.symm)
      have heq : mso G φ = mu G ψ := by
        cases hm' : mso G φ <;> cases hn' : mu G ψ <;> simp_all
      simpa only [agree,hv,↓reduceIte,beq_iff_eq] using heq
    · simp [agree,hv]

end Lax369799Proofs.FiniteTesting
