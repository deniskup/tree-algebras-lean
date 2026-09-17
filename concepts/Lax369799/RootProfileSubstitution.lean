import Lax369799.ObservedSubstitution

/-!
---
title: Initial and root observations under bounded-profile substitution
type: theorem
---
Bounded initial and root profiles suffice to transfer root observations of
substitution, including observations starting in unreachable outer components.
-/
namespace Lax369799.RootProfileSubstitution
open RankedSystems Algebras ObservedSubstitution

axiom transfer_initial_value {A B : RankedSet} (E : Algebra B) (hE : UnfoldInvariant E)
    [Finite (B 1)] (η : RankedMap A B) {V : Type} [Fintype V]
    (P : Presentation (SetSystem A) 0 V) (Q : ∀ v, SetSystem A (P.label v).1)
    (hi : ∀ v, FiniteProfiles.BoundedProfile (Nat.card (B 1) + 1)
        (fun k R => E.eval k (relabelSystem η R)) (P.label v).2 =
      FiniteProfiles.BoundedProfile (Nat.card (B 1) + 1)
        (fun k R => E.eval k (relabelSystem η R)) (Q v)) :
    PresentationObservations.values E η (FinitePresentations.flattenPresentation (finiteLabels P)) ⊆
      PresentationObservations.values E η
        (FinitePresentations.flattenPresentation (finiteLabels (replaceLabels P Q)))

axiom transfer_root_value {A B : RankedSet} (E : Algebra B) (hE : UnfoldInvariant E)
    [Finite (B 1)] (η : RankedMap A B) {V : Type} [Fintype V]
    (P : Presentation (SetSystem A) 0 V) (Q : ∀ v, SetSystem A (P.label v).1)
    (hi : ∀ v, FiniteProfiles.BoundedProfile (Nat.card (B 1) + 1)
        (fun k R => E.eval k (relabelSystem η R)) (P.label v).2 =
      FiniteProfiles.BoundedProfile (Nat.card (B 1) + 1)
        (fun k R => E.eval k (relabelSystem η R)) (Q v))
    (hr : ∀ v, FiniteProfiles.BoundedProfile (Nat.card (B 1) + 1)
        (fun k R => E.eval k (relabelSystem η R)) (uproot (P.label v).2) =
      FiniteProfiles.BoundedProfile (Nat.card (B 1) + 1)
        (fun k R => E.eval k (relabelSystem η R)) (uproot (Q v))) :
    PresentationObservations.values E η
        (RootExpansion.startAtRoots (FinitePresentations.flattenPresentation (finiteLabels P))) ⊆
      PresentationObservations.values E η (RootExpansion.startAtRoots
        (FinitePresentations.flattenPresentation (finiteLabels (replaceLabels P Q))))

end Lax369799.RootProfileSubstitution
