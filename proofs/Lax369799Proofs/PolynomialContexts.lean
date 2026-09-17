import Lax369799.PolynomialContexts
import Mathlib.Data.Finset.Basic

set_option backward.isDefEq.respectTransparency false
namespace Lax369799Proofs.PolynomialContexts
open Lax369799.RankedSystems Lax369799.Algebras Lax369799.PolynomialContexts

/--
---
conclusion: Lax369799.PolynomialContexts.composition
---
Substitute the inner polynomial for the variable, inductively through each
system evaluation in the outer polynomial.
-/
theorem composition {B : RankedSet} (E : Algebra B) {k m n : ℕ}
    {f : B m → B n} {g : B k → B m} (hf : Polynomial E m n f) (hg : Polynomial E k m g) :
    Polynomial E k n (f ∘ g) := by
  induction hf with
  | «variable» => exact hg
  | constant n b => exact .constant n b
  | evaluation P f hf ih => exact .evaluation P (fun v => f v ∘ g) ih

private theorem coordinate {A B : RankedSet} (E : Algebra B) {n : ℕ}
    (P : System A n) (q : ∀ v, B (P.val.graph.label v).1) (v : P.val.Vertex) :
    Polynomial E (P.val.graph.label v).1 n
      (fun x => E.eval n (withLabels P (Function.update q v x))) := by
  classical
  let S : Shape n := relabelSystem (fun _ _ => ()) P
  have h (w : P.val.Vertex) : Polynomial E (P.val.graph.label v).1 (P.val.graph.label w).1
      (fun x => Function.update q v x w) := by
    by_cases hw : w = v
    · subst w
      simp only [Function.update_self]
      exact Polynomial.variable
    · simpa only [Function.update_of_ne hw] using
        (Polynomial.constant (E := E) (k := (P.val.graph.label v).1) _ (q w))
  exact Polynomial.evaluation S (fun w x => Function.update q v x w) h

private theorem change_one {A B : RankedSet} (E : Algebra B) (F : Set (B 0))
    {n : ℕ} (P : System A n) (q r : ∀ v, B (P.val.graph.label v).1) (v : P.val.Vertex)
    (he : ∀ w, w ≠ v → q w = r w) (hv : Equivalent E F (q v) (r v)) :
    Equivalent E F (E.eval n (withLabels P q)) (E.eval n (withLabels P r)) := by
  classical
  intro p hp
  have hh := hv (p ∘ (fun x => E.eval n (withLabels P (Function.update q v x))))
    (composition E hp (coordinate E P q v))
  have hu : Function.update q v (r v) = r := by
    funext w
    by_cases hw : w = v
    · subst w; exact Function.update_self v (r v) q
    · rw [Function.update_of_ne hw]; exact he w hw
  simpa only [Function.comp_apply, Function.update_eq_self, hu] using hh

/--
---
conclusion: Lax369799.PolynomialContexts.evaluation_congruence
---
Vary one vertex label through a polynomial coordinate context, and compose
it with the closed testing polynomial. Replace all labels by finite induction.
-/
theorem evaluation_congruence {A B : RankedSet} (E : Algebra B) (F : Set (B 0))
    {n : ℕ} (P : System A n) (q r : ∀ v, B (P.val.graph.label v).1)
    (h : ∀ v, Equivalent E F (q v) (r v)) :
    Equivalent E F (E.eval n (withLabels P q)) (E.eval n (withLabels P r)) := by
  classical
  let mix (s : Finset P.val.Vertex) := fun v => if v ∈ s then r v else q v
  have hs (s : Finset P.val.Vertex) :
      Equivalent E F (E.eval n (withLabels P q)) (E.eval n (withLabels P (mix s))) := by
    induction s using Finset.induction_on with
    | empty =>
      simpa only [mix, Finset.notMem_empty, if_false] using
        (show Equivalent E F (E.eval n (withLabels P q)) (E.eval n (withLabels P q)) from fun _ _ => Iff.rfl)
    | @insert v s hv ih =>
      have step : Equivalent E F (E.eval n (withLabels P (mix s)))
          (E.eval n (withLabels P (mix (insert v s)))) := by
        apply change_one E F P (mix s) (mix (insert v s)) v
        · intro w hw
          simp only [mix, Finset.mem_insert, hw, false_or]
        · simpa only [mix, if_neg hv, Finset.mem_insert_self, if_true] using h v
      exact fun p hp => (ih p hp).trans (step p hp)
  simpa only [mix, Finset.mem_univ, if_true] using hs Finset.univ

end Lax369799Proofs.PolynomialContexts
