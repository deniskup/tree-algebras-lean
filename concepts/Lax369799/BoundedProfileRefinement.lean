import Lax369799.FiniteProfiles

/-!
---
title: Bounded profiles refine finite contextual equivalence
type: theorem
---
Initial and root profiles with variable-map fibres bounded by one more than
the size of the unary observing sort determine every closed contextual
acceptance test. Consequently the contextual quotient of finite presentations
is rankwise finite for every regular-tree recognizable language.
-/
namespace Lax369799.BoundedProfileRefinement
open RankedSystems Algebras FinitePresentations FiniteProfiles

axiom refines {A B : RankedSet} (E : Algebra B) (hE : UnfoldInvariant E)
    [Finite (B 1)] (η : RankedMap A B) (F : Set (B 0)) (L : Language A)
    (hL : Recognizes E η F L) {n : ℕ} (S T : FiniteSystem A n)
    (h : BoundedProfileEquivalent (Nat.card (B 1) + 1)
      (fun k R => E.eval k (relabelSystem η R)) S T) :
    FiniteContextualOrder.Equivalent (FiniteAcceptance.Accepting L) S T

axiom finite_carrier {A : RankedSet} (L : Language A) (hL : RegularTreeRecognizable L) :
    RankwiseFinite (FiniteContextualOrder.Carrier (FiniteAcceptance.Accepting L))

end Lax369799.BoundedProfileRefinement
