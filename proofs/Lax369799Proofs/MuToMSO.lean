import Lax369799.MuCalculusTheorems
import Mathlib.Data.Set.Lattice

namespace Lax369799Proofs.MuToMSO
open Lax369799
open TransitionSystems

private def conjunction {P : Type} {m n : ℕ}
    (φ ψ : MonadicSecondOrder.Formula P m n) : MonadicSecondOrder.Formula P m n :=
  .neg (.disj (.neg φ) (.neg ψ))

private def implication {P : Type} {m n : ℕ}
    (φ ψ : MonadicSecondOrder.Formula P m n) : MonadicSecondOrder.Formula P m n :=
  .disj (.neg φ) ψ

private def allVertex {P : Type} {m n : ℕ}
    (φ : MonadicSecondOrder.Formula P (m + 1) n) : MonadicSecondOrder.Formula P m n :=
  .neg (.existsVertex (.neg φ))

private def allSet {P : Type} {m n : ℕ}
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

private theorem translate_correct {P : Type} (S : TransitionSystem P) {n : ℕ}
    (φ : ModalMuCalculus.Formula P n) {m : ℕ} (x : Fin m)
    (ρ : Fin m → S.Vertex) (σ : Fin n → Set S.Vertex) :
    (translate φ x).eval S ρ σ ↔ ρ x ∈ φ.eval S σ := by
  classical
  induction φ generalizing m with
  | top => simp [translate, MonadicSecondOrder.Formula.eval, ModalMuCalculus.Formula.eval]
  | bot => simp [translate, MonadicSecondOrder.Formula.eval, ModalMuCalculus.Formula.eval]
  | proposition p => rfl
  | negProposition p => rfl
  | «variable» i => rfl
  | conj φ ψ ihφ ihψ =>
    simp [translate, conjunction, MonadicSecondOrder.Formula.eval,
      ModalMuCalculus.Formula.eval, ihφ, ihψ]
  | disj φ ψ ihφ ihψ =>
    simp [translate, MonadicSecondOrder.Formula.eval, ModalMuCalculus.Formula.eval, ihφ, ihψ]
  | diamond φ ih =>
    simp [translate, conjunction, MonadicSecondOrder.Formula.eval,
      ModalMuCalculus.Formula.eval, ih]
  | box φ ih =>
    simp [translate, allVertex, implication, MonadicSecondOrder.Formula.eval,
      ModalMuCalculus.Formula.eval, ih]
  | mu φ ih =>
    simp [translate, allSet, allVertex, implication, MonadicSecondOrder.Formula.eval,
      ModalMuCalculus.Formula.eval, ih, Set.subset_def]
  | nu φ ih =>
    simp [translate, conjunction, allVertex, implication, MonadicSecondOrder.Formula.eval,
      ModalMuCalculus.Formula.eval, ih, Set.subset_def, and_comm]

def sentence {P : Type} (φ : ModalMuCalculus.Sentence P) : MonadicSecondOrder.Sentence P :=
  .existsVertex (conjunction (.initial 0) (translate φ 0))

/--
---
conclusion: Lax369799.MuCalculusTheorems.mu_to_mso
---
Translate modalities by first-order quantification over successors. Express
a least fixed point as membership in every pre-fixed set, and a greatest
fixed point as membership in some post-fixed set. Finally designate the
initial vertex by an existential first-order variable.
-/
theorem mu_to_mso {P : Type} (φ : ModalMuCalculus.Sentence P) :
    ∃ ψ : MonadicSecondOrder.Sentence P, ∀ S,
      ModalMuCalculus.Models S φ ↔ MonadicSecondOrder.Models S ψ := by
  classical
  refine ⟨sentence φ, ?_⟩
  intro S
  simp [sentence, conjunction, MonadicSecondOrder.Models, MonadicSecondOrder.Formula.eval,
    translate_correct, ModalMuCalculus.Models]

end Lax369799Proofs.MuToMSO
