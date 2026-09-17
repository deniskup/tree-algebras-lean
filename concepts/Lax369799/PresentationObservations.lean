import Lax369799.Algebras
import Lax369799.RootExpansion

/-!
---
title: Resolution values of finite presentations
type: theorem
---
Initial observations are values of deterministic resolutions of the reachable
restriction. Root observations use roots as starting vertices. Locally
surjective maps preserve both sets of observations.
-/
namespace Lax369799.PresentationObservations
open RankedSystems Morphisms Algebras

noncomputable def values {A B : RankedSet} (E : Algebra B) (η : RankedMap A B)
    {n : ℕ} {V : Type} [Fintype V] (G : Presentation A n V) : Set (B n) :=
  {b | ∃ R : System A n, DirectResolution (trim G) R ∧ E.eval n (relabelSystem η R) = b}

axiom values_remove_roots {A B : RankedSet} (E : Algebra B) (η : RankedMap A B)
    {n : ℕ} {V : Type} [Fintype V] (G : Presentation A n V) :
    values E η { G with root := ∅ } = values E η G

axiom values_cover {A B : RankedSet} (E : Algebra B) (hE : UnfoldInvariant E)
    (η : RankedMap A B) {n : ℕ} {V W : Type} [Fintype V] [Fintype W]
    {G : Presentation A n V} {H : Presentation A n W} (f : PresentationCovers.Cover G H) :
    values E η G = values E η H

axiom root_values_cover {A B : RankedSet} (E : Algebra B) (hE : UnfoldInvariant E)
    (η : RankedMap A B) {n : ℕ} {V W : Type} [Fintype V] [Fintype W]
    {G : Presentation A n V} {H : Presentation A n W} (f : PresentationCovers.Cover G H) :
    values E η (RootExpansion.startAtRoots G) = values E η (RootExpansion.startAtRoots H)

end Lax369799.PresentationObservations
