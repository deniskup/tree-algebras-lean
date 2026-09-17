import Lax369799.AlgebraicDecomposition
import Lax369799.VariableCompression

/-!
---
title: Unary continuations of deterministic contexts
type: theorem
---
In a closed deterministic context, an outgoing direction of the hole
leads either straight back to the hole or into a deterministic unary
piece. In the former case the corresponding cut piece is empty; the
continuation is the identity and is retained by the boundary loop flag.
-/
namespace Lax369799.DeterministicPieces
open RankedSystems Flattening ContextDecomposition AlgebraicDecomposition

axiom direction_piece {A : RankedSet} {k : ℕ} (C : SetContext A k 0)
    (hC : C.system.Deterministic) (i : Fin k) :
    (i ∈ (boundary C).loops ∧ (trim (ordinaryPiece C i.succ)).size = 0) ∨
    (i ∉ (boundary C).loops ∧ (trim (ordinaryPiece C i.succ)).Deterministic)

axiom entry_piece {A : RankedSet} {k : ℕ} (C : SetContext A k 0)
    (hC : C.system.Deterministic) :
    ((boundary C).initial ∧ (trim (ordinaryPiece C 0)).size = 0) ∨
    (¬ (boundary C).initial ∧ (trim (ordinaryPiece C 0)).Deterministic)

/-- `none` is the identity continuation, represented by a direct boundary connection. -/
noncomputable def continuation {A : RankedSet} {k : ℕ} (C : SetContext A k 0)
    (i : Fin (k + 1)) : Option (System A 1) := by
  classical
  exact if h : (trim (ordinaryPiece C i)).Deterministic then
    some ⟨trim (ordinaryPiece C i), h⟩ else none

axiom continuation_boundary {A : RankedSet} {k : ℕ} (C : SetContext A k 0)
    (hC : C.system.Deterministic) :
    (continuation C 0 = none ↔ (boundary C).initial) ∧
    ∀ i : Fin k, continuation C i.succ = none ↔ i ∈ (boundary C).loops

axiom compress_continuations {A : RankedSet} {V : Type} [Finite V] {m n : ℕ}
    (C : SetContext A m 0) (hC : C.system.Deterministic)
    (σ : Fin m → Fin n) (ρ : System A 1 → V) :
    ∃ (m' : ℕ) (τ : Fin m → Fin m') (sectionMap : Fin m' → Fin m),
      (∀ j, τ (sectionMap j) = j) ∧
      (∀ i, σ (sectionMap (τ i)) = σ i) ∧
      (∀ i, (continuation C (sectionMap (τ i)).succ).map ρ =
        (continuation C i.succ).map ρ) ∧
      (∀ i, sectionMap (τ i) ∈ (boundary C).loops ↔ i ∈ (boundary C).loops) ∧
      (∀ j, Nat.card {i // σ (sectionMap i) = j} ≤ Nat.card V + 1)

end Lax369799.DeterministicPieces
