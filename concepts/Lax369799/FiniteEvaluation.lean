import Lax369799.FiniteSyntacticAlgebra

/-!
---
title: Context evaluation in finite-presentation algebras
type: theorem
---
Associativity makes context evaluation depend only on the value of the
inserted presentation. Testing quotient values in all algebra contexts
recovers their contextual order.
-/
namespace Lax369799.FiniteEvaluation
open RankedSystems (RankedSet RankedMap)
open FinitePresentations FiniteContexts FiniteContextualOrder FiniteSyntacticAlgebra

axiom context_evaluation {A : RankedSet} (E : Algebra A) {k n : ℕ}
    (C : Context A k n) (S : FiniteSystem A k) :
    E.eval n (plug C S) = E.eval n (plug C (atomic (E.eval k S)))

def quotientContext {A : RankedSet} (F : ClosedProperty A) {k n : ℕ}
    (C : Context A k n) : Context (Carrier F) k n where
  system := relabel (fun r => Sum.map (fun a => quotientMap F r (atomic a)) id) C.system
  one_hole := by
    have hh (v : C.system.Vertex) :
        Lax369799.Flattening.IsHole
          ((relabel (fun r => Sum.map (fun a => quotientMap F r (atomic a)) id) C.system).graph.label v) ↔
        Lax369799.Flattening.IsHole (C.system.graph.label v) := by
      change (∃ h, Sum.map (fun a => quotientMap F (C.system.graph.label v).1 (atomic a)) id
        (C.system.graph.label v).2 = Sum.inr h) ↔
        (∃ h, (C.system.graph.label v).2 = Sum.inr h)
      generalize C.system.graph.label v = t
      obtain ⟨r, a⟩ := t
      cases a <;> simp
    obtain ⟨v, hv, hu⟩ := C.one_hole
    exact ⟨v, (hh v).mpr hv, fun w hw => hu w ((hh w).mp hw)⟩

axiom quotient_context {A : RankedSet} (F : ClosedProperty A)
    (E : Algebra (Carrier F))
    (hE : ∀ n (S : FiniteSystem (FiniteSystem A) n),
      E.eval n (relabel (quotientMap F) S) = quotientMap F n (flatten S))
    {k n : ℕ} (C : Context A k n) (S : FiniteSystem A k) :
    E.eval n (plug (quotientContext F C) (atomic (quotientMap F k S))) =
      quotientMap F n (plug C S)

axiom order_separating {A : RankedSet} (F : ClosedProperty A) (hF : IsoInvariant F)
    (E : Algebra (Carrier F))
    (hE : ∀ n (S : FiniteSystem (FiniteSystem A) n),
      E.eval n (relabel (quotientMap F) S) = quotientMap F n (flatten S))
    {n : ℕ} (a b : Carrier F n)
    (h : ∀ C : Context (Carrier F) n 0,
      AcceptingClass F (E.eval 0 (plug C (atomic a))) →
      AcceptingClass F (E.eval 0 (plug C (atomic b)))) : ClassBelow F a b

end Lax369799.FiniteEvaluation
