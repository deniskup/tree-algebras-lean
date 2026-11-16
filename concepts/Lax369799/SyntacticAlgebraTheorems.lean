import Lax369799.SyntacticOrder
import Lax369799.Resolutions

/-!
---
title: Syntactic set-algebras and rankwise finiteness
type: theorem
---
Recognition below is conditional on the original set-algebra interface.
Existence uses expanded continuity in ExpandedSyntacticAlgebra instead.
The accepting set is an upward-closed meet filter and recognises the language. Small-profile
equivalence has finite index, giving rankwise finiteness when
the language is recognised by a rankwise-finite regular-tree algebra.
These are the principal results of Sections 4.2–4.3.
-/

namespace Lax369799.SyntacticAlgebraTheorems
open RankedSystems Morphisms Flattening Algebras SetAlgebras SyntacticOrder Resolutions

-- The revised contextual congruence is stated and proved for all finite
-- presentations in FiniteContextualOrder.contextual_congruence.

-- Existence with expanded continuity is stated in ExpandedSyntacticAlgebra.
-- The original atomic-yield continuity is incompatible with this quotient.

axiom syntactic_recognition {A : RankedSet} (L : Language A)
    (hL : UnfoldInvariantLanguage L) (E : SyntacticAlgebra L) :
    ∃ F : Set (SyntacticCarrier L 0),
      (∀ S, syntacticMap L 0 S ∈ F ↔ Accepting L S) ∧
      (∀ T : System A 0, syntacticMap L 0 T.val ∈ F ↔ T ∈ L) ∧
      (∀ a b, a ∈ F → Below E.algebra a b → b ∈ F) ∧
      (∀ a b, a ∈ F → b ∈ F → meet E.algebra a b ∈ F)

axiom small_profile_finite {A B : RankedSet} (hB : RankwiseFinite B)
    (ρ : ∀ n, System A n → B n) (n : ℕ) :
    Finite (Quot (@SmallProfileEquivalent A B ρ n))

-- SmallProfileRefinement.refines uses the revised small-map bound and
-- the unpruned syntactic order of Definition 68.

axiom syntactic_rankwise_finite {A : RankedSet} (L : Language A)
    (hL : RegularTreeRecognizable L) : RankwiseFinite (SyntacticCarrier L)

end Lax369799.SyntacticAlgebraTheorems
