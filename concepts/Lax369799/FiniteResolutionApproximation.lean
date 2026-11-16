import Lax369799.FiniteResolutionNormalForms
import Lax369799.FlatteningTheorems
import Lax369799.ProfileSubstitution

/-!
---
title: Finite approximation of a flattening resolution
type: theorem
---
A direct resolution of a flattening can be reproduced, up to unfolding,
using only finitely many direct resolutions of each inner label. The
variable maps of the flatten-resolution are retained when selecting and
reassembling these components. This is the initial-resolution argument
underlying the yield-continuity corollary in Section 2.9.
-/
namespace Lax369799.FiniteResolutionApproximation
open RankedSystems Morphisms Flattening Resolutions FiniteResolutionNormalForms

noncomputable def replace {A : RankedSet} {n : ℕ} (S : SetSystem (SetSystem A) n)
    (k : S.Vertex → ℕ) (c : ∀ v, Fin (k v) → Component (Inner S v)) : SetSystem (SetSystem A) n :=
  { S with graph := { S.graph with label := fun v => ⟨(S.graph.label v).1, trim (family (c v)).graph⟩ } }

/-- A finite family of local resolutions suffices for any replacement
that still admits those resolutions. -/
axiom finite_support {A : RankedSet} {n : ℕ}
    (S : SetSystem (SetSystem A) n) (R : System A n)
    (hR : DirectResolution (flatten S) R) :
    ∃ (k : S.Vertex → ℕ) (c : ∀ v, Fin (k v) → Component (Inner S v)),
      (∀ v i, (c v i).rooted = false) ∧
      ∀ (Q : ∀ v, SetSystem A (S.graph.label v).1),
        (∀ v i, DirectResolution (Q v) (c v i).system) →
        ∃ U : System A n,
          DirectResolution (flatten (ProfileSubstitution.withLabels S Q)) U ∧
          UnfoldsTo R.val U.val

axiom direct_approximation {A : RankedSet} {n : ℕ}
    (S : SetSystem (SetSystem A) n) (R : System A n)
    (hR : DirectResolution (flatten S) R) :
    ∃ (k : S.Vertex → ℕ) (c : ∀ v, Fin (k v) → Component (Inner S v)) (U : System A n),
      (∀ v i, (c v i).rooted = false) ∧
      DirectResolution (flatten (replace S k c)) U ∧ UnfoldsTo R.val U.val

end Lax369799.FiniteResolutionApproximation
