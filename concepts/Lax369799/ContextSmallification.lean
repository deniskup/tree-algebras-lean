import Lax369799.DeterministicNormalForms
import Lax369799.ContextRelabelling

/-!
---
title: Smallification preserving identity continuations
type: theorem
---
Variables can be grouped by their target and their optional unary
continuation value. The grouping preserves evaluation in a closed
deterministic context and has at most |A₁|+1 representatives over each
target. The additional observation represents a direct return to the
hole, whose cut piece is empty.
-/
namespace Lax369799.ContextSmallification
open RankedSystems Flattening Algebras Renaming

axiom context_smallification {A : RankedSet} (E : Algebra A) (hE : UnfoldInvariant E)
    [Finite (A 1)] {m n : ℕ} (C : SetContext A m 0) (hC : C.system.Deterministic)
    (S : System A m) (σ : Fin m → Fin n) :
    ∃ (m' : ℕ) (τ : Fin m → Fin m') (sectionMap : Fin m' → Fin m),
      (∀ j, τ (sectionMap j) = j) ∧
      (∀ i, σ (sectionMap (τ i)) = σ i) ∧
      (∀ j, Nat.card {i // σ (sectionMap i) = j} ≤ Nat.card (A 1) + 1) ∧
      ∃ U V : System A 0,
        U.val = plug C S.val ∧
        V.val = plug C (renameSystem (sectionMap ∘ τ) S).val ∧
        E.eval 0 U = E.eval 0 V

axiom mapped_context_smallification {A B : RankedSet} (E : Algebra B) (hE : UnfoldInvariant E)
    [Finite (B 1)] (η : RankedMap A B) {m n : ℕ}
    (C : SetContext A m 0) (hC : C.system.Deterministic) (S : System A m) (σ : Fin m → Fin n) :
    ∃ (m' : ℕ) (τ : Fin m → Fin m') (sectionMap : Fin m' → Fin m),
      (∀ j, τ (sectionMap j) = j) ∧
      (∀ i, σ (sectionMap (τ i)) = σ i) ∧
      (∀ j, Nat.card {i // σ (sectionMap i) = j} ≤ Nat.card (B 1) + 1) ∧
      ∃ U V : System A 0,
        U.val = plug C S.val ∧
        V.val = plug C (renameSystem (sectionMap ∘ τ) S).val ∧
        E.eval 0 (relabelSystem η U) = E.eval 0 (relabelSystem η V)

end Lax369799.ContextSmallification
