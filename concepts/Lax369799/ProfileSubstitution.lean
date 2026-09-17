import Lax369799.OptimalResolutions
import Lax369799.FiniteProfiles

/-!
---
title: Transfer of resolutions through bounded profiles
type: theorem
---
An inner set-system can be replaced by another with the same bounded
profile. A resolution of the closed flattening then has a resolution of
the replacement with the same value in the observing algebra. The proof
uses factorisation into local resolutions followed by bounded optimal
flatten-resolution replacement.
-/
namespace Lax369799.ProfileSubstitution
open RankedSystems Flattening Morphisms Algebras

def withLabels {A B : RankedSet} {n : ℕ} (S : SetSystem A n)
    (f : ∀ v, B (S.graph.label v).1) : SetSystem B n where
  size := S.size
  graph := { S.graph with label := fun v => ⟨(S.graph.label v).1, f v⟩ }
  reachable := S.reachable

axiom transfer_resolution {A B : RankedSet} (E : Algebra B) (hE : UnfoldInvariant E)
    [Finite (B 1)] (η : RankedMap A B) (P : SetSystem (SetSystem A) 0)
    (Q : ∀ v, SetSystem A (P.graph.label v).1)
    (hQ : ∀ v, FiniteProfiles.BoundedProfile (Nat.card (B 1) + 1)
        (fun k R => E.eval k (relabelSystem η R)) (Inner P v) =
      FiniteProfiles.BoundedProfile (Nat.card (B 1) + 1)
        (fun k R => E.eval k (relabelSystem η R)) (Q v))
    (R : System A 0) (hR : DirectResolution (flatten P) R) :
    ∃ U : System A 0, DirectResolution (flatten (withLabels P Q)) U ∧
      E.eval 0 (relabelSystem η R) = E.eval 0 (relabelSystem η U)

end Lax369799.ProfileSubstitution
