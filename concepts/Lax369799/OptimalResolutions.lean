import Lax369799.ContextSmallification
import Lax369799.ResolutionCompression

/-!
---
title: Bounded optimal flatten-resolutions
type: theorem
---
Every closed flatten-resolution can be replaced by one whose variable-map
fibres have at most |B₁|+1 elements, preserving the value of its flattening
in an unfold-invariant observing algebra. The additional observation
retains identity continuations at direct hole loops. Only the unary sort
needs to be finite for this step.
-/
namespace Lax369799.OptimalResolutions
open RankedSystems Flattening Resolutions Algebras

def BoundedMap {m n : ℕ} (bound : ℕ) (σ : Fin m → Fin n) : Prop :=
  ∀ j, Nat.card {i // σ i = j} ≤ bound

axiom optimal_flatten_resolution {A B : RankedSet} (E : Algebra B) (hE : UnfoldInvariant E)
    [Finite (B 1)] (η : RankedMap A B) (S : SetSystem (SetSystem A) 0)
    (T : System (System A) 0) (r : FlattenResolution S T)
    (R : System A 0) (hR : SystemFlattening T R) :
    ∃ (U : System (System A) 0) (V : System A 0) (r' : FlattenResolution S U),
      SystemFlattening U V ∧
      (∀ v, BoundedMap (Nat.card (B 1) + 1) (r'.variableMap v)) ∧
      E.eval 0 (relabelSystem η R) = E.eval 0 (relabelSystem η V)

end Lax369799.OptimalResolutions
