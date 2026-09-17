import Lax369799.SyntacticOrder
import Lax369799.Resolutions

/-!
---
title: Syntactic set-algebras and rankwise finiteness
type: theorem
---
For an unfold-invariant language, the yield-syntactic quotient carries a
set-algebra whose order is the syntactic preorder. Its accepting set is an
upward-closed meet filter and recognises the language. Small-profile
equivalence refines syntactic equivalence, giving rankwise finiteness when
the language is recognised by a rankwise-finite regular-tree algebra.
These are the principal results of Sections 4.2–4.3.
-/

namespace Lax369799.SyntacticAlgebraTheorems
open RankedSystems Morphisms Flattening Algebras SetAlgebras SyntacticOrder Resolutions

axiom syntactic_congruence {A : RankedSet} (L : Language A)
    (hL : UnfoldInvariantLanguage L) {k n : ℕ} (C : SetContext A k n)
    (S T : SetSystem A k) (h : SyntacticBelow L S T) :
    SyntacticBelow L (plug C S) (plug C T)

axiom syntactic_algebra_exists {A : RankedSet} (L : Language A)
    (hL : UnfoldInvariantLanguage L) :
    ∃ E : SyntacticAlgebra L, ∀ n (S T : SetSystem A n),
      Below E.algebra (syntacticMap L n S) (syntacticMap L n T) ↔ SyntacticBelow L S T

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

axiom small_profile_refines {A B : RankedSet} (E : Algebra B)
    (hB : RankwiseFinite B) (hE : UnfoldInvariant E) (η : RankedMap A B)
    (F : Set (B 0)) (L : Language A) (hL : Algebras.Recognizes E η F L)
    {n : ℕ} (S T : SetSystem A n)
    (h : SmallProfileEquivalent (fun n U => E.eval n (relabelSystem η U)) S T) :
    SyntacticEquivalent L S T

axiom syntactic_rankwise_finite {A : RankedSet} (L : Language A)
    (hL : RegularTreeRecognizable L) : RankwiseFinite (SyntacticCarrier L)

end Lax369799.SyntacticAlgebraTheorems
