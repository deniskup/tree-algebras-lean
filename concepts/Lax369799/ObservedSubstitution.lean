import Lax369799.PresentationObservations
import Lax369799.ProfileSubstitution

/-!
---
title: Bounded profiles in root-free substitution patterns
type: theorem
---
A finite outer presentation need not be reachable. If its inner set-systems
have no roots, equality of their bounded initial profiles suffices to
transfer every observed value of the closed substitution.
-/
namespace Lax369799.ObservedSubstitution
open RankedSystems Algebras

def finiteLabels {A : RankedSet} {n : ℕ} {V : Type}
    (P : Presentation (SetSystem A) n V) :
    Presentation (FinitePresentations.FiniteSystem A) n V := {
  P with label := fun v => ⟨(P.label v).1, FinitePresentations.ofSetSystem (P.label v).2⟩ }

def replaceLabels {A : RankedSet} {n : ℕ} {V : Type}
    (P : Presentation (SetSystem A) n V) (Q : ∀ v, SetSystem A (P.label v).1) :
    Presentation (SetSystem A) n V := { P with label := fun v => ⟨(P.label v).1, Q v⟩ }

axiom transfer_value {A B : RankedSet} (E : Algebra B) (hE : UnfoldInvariant E)
    [Finite (B 1)] (η : RankedMap A B) {V : Type} [Fintype V]
    (P : Presentation (SetSystem A) 0 V) (Q : ∀ v, SetSystem A (P.label v).1)
    (hP : ∀ v, (P.label v).2.graph.root = ∅) (hQ : ∀ v, (Q v).graph.root = ∅)
    (h : ∀ v, FiniteProfiles.BoundedProfile (Nat.card (B 1) + 1)
        (fun k R => E.eval k (relabelSystem η R)) (P.label v).2 =
      FiniteProfiles.BoundedProfile (Nat.card (B 1) + 1)
        (fun k R => E.eval k (relabelSystem η R)) (Q v)) :
    PresentationObservations.values E η (FinitePresentations.flattenPresentation (finiteLabels P)) ⊆
      PresentationObservations.values E η
        (FinitePresentations.flattenPresentation (finiteLabels (replaceLabels P Q)))

end Lax369799.ObservedSubstitution
