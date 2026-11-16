import Lax369799.SupportedYields
import Lax369799.SupportedCompletion
import Lax369799.Resolutions
import Lax369799.FiniteProfiles

/-!
---
title: Profiles of fully supported resolutions
type: theorem
---
The profiles of Section 4.3 record a value in the original supported
algebra and the variable map of a fully supported resolution. Root
profiles start at the root marks. Small profiles restrict each fibre
to the revised bound |B₀| + |B₁| + 1.
-/

namespace Lax369799.SupportedProfiles
open RankedSystems (RankedSet RankedMap)
open FinitePresentations FiniteMorphisms SupportedMorphisms FiniteRenaming

def Profile {A B : RankedSet} (E : SupportedAlgebras.Algebra B) (η : RankedMap A B)
    {n : ℕ} (S : FiniteSystem A n) : Set (Resolutions.ProfileEntry B n) :=
  {e | ∃ T : SupportedSystems.System A e.1,
    Nonempty (Morphism (push e.2.2 (presentation T)) S) ∧
      E.eval e.1 (SupportedSystems.relabel η T) = e.2.1}

def ProfileEquivalent {A B : RankedSet} (E : SupportedAlgebras.Algebra B) (η : RankedMap A B)
    {n : ℕ} (S T : FiniteSystem A n) : Prop :=
  Profile E η S = Profile E η T ∧
    Profile E η (SupportedYields.uproot S) = Profile E η (SupportedYields.uproot T)

def SmallProfile {A B : RankedSet} (E : SupportedAlgebras.Algebra B) (η : RankedMap A B)
    {n : ℕ} (S : FiniteSystem A n) : Set (Resolutions.ProfileEntry B n) :=
  {e | e ∈ Profile E η S ∧ Resolutions.SmallMap B e.2.2}

def SmallProfileEquivalent {A B : RankedSet} (E : SupportedAlgebras.Algebra B) (η : RankedMap A B)
    {n : ℕ} (S T : FiniteSystem A n) : Prop :=
  SmallProfile E η S = SmallProfile E η T ∧
    SmallProfile E η (SupportedYields.uproot S) = SmallProfile E η (SupportedYields.uproot T)

open RankedSystems (System RankwiseFinite relabelSystem trim)
open SupportEvaluation (Carrier classMap)

axiom full_completion {A B : RankedSet} (E : SupportedAlgebras.Algebra B)
    (η : RankedMap A B) (D : Algebras.Algebra (Carrier E)) (hDE : Algebras.UnfoldInvariant D)
    (hD : ∀ n (R : System B n),
      D.eval n (relabelSystem (SupportedCompletion.letter E) R) = classMap E n R)
    {n : ℕ} (S T : FiniteSystem A n) (h : ProfileEquivalent E η S T) :
    Resolutions.ProfileEquivalent
      (fun k R => D.eval k (relabelSystem (fun j a => SupportedCompletion.letter E j (η j a)) R))
      (trim S.graph) (trim T.graph)

axiom small_completion {A B : RankedSet} (E : SupportedAlgebras.Algebra B)
    (hB : RankwiseFinite B) (η : RankedMap A B) (D : Algebras.Algebra (Carrier E))
    (hDE : Algebras.UnfoldInvariant D)
    (hD : ∀ n (R : System B n),
      D.eval n (relabelSystem (SupportedCompletion.letter E) R) = classMap E n R)
    {n : ℕ} (S T : FiniteSystem A n) (h : SmallProfileEquivalent E η S T) :
    FiniteProfiles.BoundedProfileEquivalent (Nat.card (Carrier E 1) + 1)
      (fun k R => D.eval k (relabelSystem (fun j a => SupportedCompletion.letter E j (η j a)) R)) S T

axiom full_refines {A B : RankedSet} (E : SupportedAlgebras.Algebra B)
    (hB : RankwiseFinite B) (hE : SupportedAlgebras.UnfoldInvariant E)
    (η : RankedMap A B) (F : Set (B 0)) (L : Algebras.Language A)
    (hL : SupportedAlgebras.Recognizes E η F L) {n : ℕ} (S T : FiniteSystem A n)
    (h : ProfileEquivalent E η S T) :
    FiniteContextualOrder.Equivalent (FiniteAcceptance.Accepting L) S T

axiom small_refines {A B : RankedSet} (E : SupportedAlgebras.Algebra B)
    (hB : RankwiseFinite B) (hE : SupportedAlgebras.UnfoldInvariant E)
    (η : RankedMap A B) (F : Set (B 0)) (L : Algebras.Language A)
    (hL : SupportedAlgebras.Recognizes E η F L) {n : ℕ} (S T : FiniteSystem A n)
    (h : SmallProfileEquivalent E η S T) :
    FiniteContextualOrder.Equivalent (FiniteAcceptance.Accepting L) S T

axiom yield_profile {A B : RankedSet} (E : SupportedAlgebras.Algebra B)
    (hE : SupportedAlgebras.UnfoldInvariant E) (η : RankedMap A B) {n : ℕ}
    (S : FiniteSystem A n) (e : Resolutions.ProfileEntry B n) :
    e ∈ Profile E η S ↔
      ∃ T : SupportedSystems.System A e.1, SupportedYields.InitialYield S T e.2.2 ∧
        E.eval e.1 (SupportedSystems.relabel η T) = e.2.1

axiom closed_small_profile {A B : RankedSet} (E : SupportedAlgebras.Algebra B)
    (η : RankedMap A B) (S : FiniteSystem A 0) :
    SmallProfile E η S = Profile E η S

axiom small_profile_finite {A B : RankedSet} (E : SupportedAlgebras.Algebra B)
    (hB : RankwiseFinite B) (η : RankedMap A B) (n : ℕ) :
    Finite (Quot (@SmallProfileEquivalent A B E η n))

axiom closed_congruence {A B : RankedSet} (E : SupportedAlgebras.Algebra B)
    (hB : RankwiseFinite B) (hE : SupportedAlgebras.UnfoldInvariant E) (η : RankedMap A B)
    (P : FiniteSystem (FiniteSystem A) 0) (Q : ∀ v, FiniteSystem A (P.graph.label v).1)
    (h : ∀ v, SmallProfileEquivalent E η (Inner P.graph v) (Q v)) :
    ProfileEquivalent E η (flatten P) (flatten (withLabels P Q))

axiom congruence {A B : RankedSet} (E : SupportedAlgebras.Algebra B)
    (hE : SupportedAlgebras.UnfoldInvariant E) (η : RankedMap A B) {n : ℕ}
    (P : FiniteSystem (FiniteSystem A) n) (Q : ∀ v, FiniteSystem A (P.graph.label v).1)
    (h : ∀ v, ProfileEquivalent E η (Inner P.graph v) (Q v)) :
    ProfileEquivalent E η (flatten P) (flatten (withLabels P Q))

end Lax369799.SupportedProfiles
