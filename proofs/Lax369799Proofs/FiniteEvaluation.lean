import Lax369799.FiniteEvaluation
import Lax369799Proofs.FiniteSyntacticAlgebra

namespace Lax369799Proofs.FiniteEvaluation
open Lax369799.RankedSystems (RankedSet RankedMap)
open Lax369799.FinitePresentations Lax369799.FiniteContexts
open Lax369799.FiniteContextualOrder Lax369799.FiniteSyntacticAlgebra
open Lax369799.FiniteEvaluation (quotientContext)

/--
---
conclusion: Lax369799.FiniteEvaluation.context_evaluation
---
Evaluate the substituted labels first. The unit law gives the same label
values after replacing the hole's argument by an atomic presentation.
-/
theorem context_evaluation {A : RankedSet} (E : Algebra A) {k n : ℕ}
    (C : Context A k n) (S : FiniteSystem A k) :
    E.eval n (plug C S) = E.eval n (plug C (atomic (E.eval k S))) := by
  rw [plug, plug, ← E.associative, ← E.associative]
  apply congrArg (E.eval n)
  change relabel (fun r a => E.eval r (substitution S r a)) C.system =
    relabel (fun r a => E.eval r (substitution (atomic (E.eval k S)) r a)) C.system
  have he : (fun r a => E.eval r (substitution S r a)) =
      (fun r a => E.eval r (substitution (atomic (E.eval k S)) r a)) := by
    funext r a
    cases a with
    | inl a => rfl
    | inr h => obtain ⟨he⟩ := h; subst r; exact (E.unit k (E.eval k S)).symm
  rw [he]

/--
---
conclusion: Lax369799.FiniteEvaluation.quotient_context
---
Lift ordinary labels to their atomic classes and the hole argument to its
class. Associativity, the unit law, and the quotient evaluation equation
identify this evaluation with the class of the substituted presentation.
-/
theorem quotient_context {A : RankedSet} (F : ClosedProperty A)
    (E : Algebra (Carrier F))
    (hE : ∀ n (S : FiniteSystem (FiniteSystem A) n),
      E.eval n (relabel (quotientMap F) S) = quotientMap F n (flatten S))
    {k n : ℕ} (C : Context A k n) (S : FiniteSystem A k) :
    E.eval n (plug (quotientContext F C) (atomic (quotientMap F k S))) =
      quotientMap F n (plug C S) := by
  rw [plug, ← E.associative, plug, ← hE]
  apply congrArg (E.eval n)
  dsimp only [relabel, quotientContext]
  congr 1
  congr 1
  funext v
  rcases h : C.system.graph.label v with ⟨r, a⟩
  cases a with
  | inl a => simp [substitution, E.unit]
  | inr h' =>
    obtain ⟨he⟩ := h'
    subst r
    simp [substitution, E.unit]

/--
---
conclusion: Lax369799.FiniteEvaluation.order_separating
---
Every base-alphabet context lifts to a context over the quotient carrier.
Its evaluation on representatives is exactly their substituted class, so
acceptance implications imply the defining contextual preorder.
-/
theorem order_separating {A : RankedSet} (F : ClosedProperty A) (hF : IsoInvariant F)
    (E : Algebra (Carrier F))
    (hE : ∀ n (S : FiniteSystem (FiniteSystem A) n),
      E.eval n (relabel (quotientMap F) S) = quotientMap F n (flatten S))
    {n : ℕ} (a b : Carrier F n)
    (h : ∀ C : Context (Carrier F) n 0,
      AcceptingClass F (E.eval 0 (plug C (atomic a))) →
      AcceptingClass F (E.eval 0 (plug C (atomic b)))) : ClassBelow F a b := by
  induction a using Quot.inductionOn with
  | h S =>
    induction b using Quot.inductionOn with
    | h T =>
      intro C hc
      have hh := h (quotientContext F C)
      change AcceptingClass F (E.eval 0 (plug (quotientContext F C) (atomic (quotientMap F n S)))) →
        AcceptingClass F (E.eval 0 (plug (quotientContext F C) (atomic (quotientMap F n T)))) at hh
      rw [quotient_context F E hE, quotient_context F E hE] at hh
      have ha := (FiniteSyntacticAlgebra.accepting_classes F hF).1
      exact (ha _).mp (hh ((ha _).mpr hc))

end Lax369799Proofs.FiniteEvaluation
