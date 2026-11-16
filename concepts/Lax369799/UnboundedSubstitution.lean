import Lax369799.RootProfileSubstitution

/-!
---
title: Full-profile transfer in every output rank
type: theorem
---
Full local profiles preserve the values of resolutions under substitution.
The proof requires no finite bound on local variable maps. Both initial
and root observations are covered for arbitrary finite presentations,
including unreachable vertices, in every output rank.
-/

namespace Lax369799.UnboundedSubstitution
open RankedSystems Morphisms Algebras Flattening Resolutions ProfileSubstitution
open ObservedSubstitution PresentationObservations RootExpansion

axiom transfer_resolution {A B : RankedSet} (E : Algebra B) (hE : UnfoldInvariant E)
    (η : RankedMap A B) {n : ℕ} (P : SetSystem (SetSystem A) n)
    (Q : ∀ v, SetSystem A (P.graph.label v).1)
    (hQ : ∀ v, Profile
        (fun k R => E.eval k (relabelSystem η R)) (Inner P v) =
      Profile
        (fun k R => E.eval k (relabelSystem η R)) (Q v))
    (R : System A n) (hR : DirectResolution (flatten P) R) :
    ∃ U : System A n, DirectResolution (flatten (withLabels P Q)) U ∧
      E.eval n (relabelSystem η R) = E.eval n (relabelSystem η U)

axiom transfer_value {A B : RankedSet} (E : Algebra B) (hE : UnfoldInvariant E)
    (η : RankedMap A B) {n : ℕ} {V : Type} [Fintype V]
    (P : Presentation (SetSystem A) n V) (Q : ∀ v, SetSystem A (P.label v).1)
    (hP : ∀ v, (P.label v).2.graph.root = ∅) (hQ : ∀ v, (Q v).graph.root = ∅)
    (h : ∀ v, Profile
        (fun k R => E.eval k (relabelSystem η R)) (P.label v).2 =
      Profile
        (fun k R => E.eval k (relabelSystem η R)) (Q v)) :
    values E η (Lax369799.FinitePresentations.flattenPresentation (finiteLabels P)) ⊆
      values E η (Lax369799.FinitePresentations.flattenPresentation (finiteLabels (replaceLabels P Q)))

axiom transfer_initial_value {A B : RankedSet} (E : Algebra B) (hE : UnfoldInvariant E)
    (η : RankedMap A B) {n : ℕ} {V : Type} [Fintype V]
    (P : Presentation (SetSystem A) n V) (Q : ∀ v, SetSystem A (P.label v).1)
    (hi : ∀ v, Profile
        (fun k R => E.eval k (relabelSystem η R)) (P.label v).2 =
      Profile
        (fun k R => E.eval k (relabelSystem η R)) (Q v)) :
    values E η (Lax369799.FinitePresentations.flattenPresentation (finiteLabels P)) ⊆
      values E η (Lax369799.FinitePresentations.flattenPresentation (finiteLabels (replaceLabels P Q)))

axiom transfer_root_value {A B : RankedSet} (E : Algebra B) (hE : UnfoldInvariant E)
    (η : RankedMap A B) {n : ℕ} {V : Type} [Fintype V]
    (P : Presentation (SetSystem A) n V) (Q : ∀ v, SetSystem A (P.label v).1)
    (hi : ∀ v, Profile
        (fun k R => E.eval k (relabelSystem η R)) (P.label v).2 =
      Profile
        (fun k R => E.eval k (relabelSystem η R)) (Q v))
    (hr : ∀ v, Profile
        (fun k R => E.eval k (relabelSystem η R)) (uproot (P.label v).2) =
      Profile
        (fun k R => E.eval k (relabelSystem η R)) (uproot (Q v))) :
    values E η (startAtRoots (Lax369799.FinitePresentations.flattenPresentation (finiteLabels P))) ⊆
      values E η (startAtRoots (Lax369799.FinitePresentations.flattenPresentation
        (finiteLabels (replaceLabels P Q))))

end Lax369799.UnboundedSubstitution
