import Lax369799.FiniteMorphisms
import Lax369799.SyntacticAlgebraTheorems

/-!
---
title: Small profiles of finite presentations
type: theorem
---
Initial and root profiles observe the reachable restriction of a finite
presentation. Their small versions range over a finite set when every
sort of the observing algebra is finite. Every contextual class also has
a reachable representative.
-/
namespace Lax369799.FiniteProfiles
open RankedSystems (RankedSet RankwiseFinite)
open FinitePresentations FiniteContextualOrder FiniteAcceptance

def SmallProfileEquivalent {A B : RankedSet}
    (ρ : ∀ n, RankedSystems.System A n → B n) {n : ℕ} (S T : FiniteSystem A n) : Prop :=
  Resolutions.SmallProfileEquivalent ρ (RankedSystems.trim S.graph) (RankedSystems.trim T.graph)

axiom small_profile_finite {A B : RankedSet} (hB : RankwiseFinite B)
    (ρ : ∀ n, RankedSystems.System A n → B n) (n : ℕ) :
    Finite (Quot (@SmallProfileEquivalent A B ρ n))

axiom reachable_representative {A : RankedSet} (L : Algebras.Language A) {n : ℕ}
    (a : Carrier (Accepting L) n) :
    ∃ S : RankedSystems.SetSystem A n, quotientMap (Accepting L) n (ofSetSystem S) = a

end Lax369799.FiniteProfiles
