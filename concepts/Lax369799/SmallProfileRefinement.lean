import Lax369799.BoundedProfileRefinement

/-!
---
title: Small profiles and the yield-syntactic congruence
type: theorem
---
The small-map bound b_A is |A₀| + |A₁| + 1 in Section 4.3. Equality of
initial and root profiles restricted to these maps determines every
closed contextual acceptance test. Thus small-profile equivalence
refines the yield-syntactic equivalence (Corollary 84), and has finite
index in every rank when the observing algebra is rankwise finite.
Contexts and substitution retain all vertices, as in Definition 68.
-/

namespace Lax369799.SmallProfileRefinement
open RankedSystems Algebras FinitePresentations

axiom refines {A B : RankedSet} (E : Algebra B) (hB : RankwiseFinite B)
    (hE : UnfoldInvariant E) (η : RankedMap A B) (F : Set (B 0)) (L : Language A)
    (hL : Recognizes E η F L) {n : ℕ} (S T : FiniteSystem A n)
    (h : FiniteProfiles.SmallProfileEquivalent
      (fun k R => E.eval k (relabelSystem η R)) S T) :
    FiniteContextualOrder.Equivalent (FiniteAcceptance.Accepting L) S T

end Lax369799.SmallProfileRefinement
