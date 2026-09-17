import Lax369799.ObservedSubstitution
import Lax369799.RootlessFlattening
import Lax369799Proofs.PresentationObservations
import Lax369799Proofs.FiniteOuterMorphisms

set_option backward.isDefEq.respectTransparency false

namespace Lax369799Proofs.ObservedSubstitution
open Lax369799.RankedSystems Lax369799.Algebras
open Lax369799.ObservedSubstitution Lax369799.PresentationObservations
open Lax369799Proofs.Pullbacks

noncomputable def outerCover {A : RankedSet} {n : ℕ} {V : Type} [Fintype V]
    (P : Presentation (SetSystem A) n V) (hP : ∀ v, (P.label v).2.graph.root = ∅) :
    Lax369799.PresentationCovers.Cover (Flattening.graph (trim P))
      (Lax369799.FinitePresentations.flattenPresentation (finiteLabels P)) :=
  FiniteOuterMorphisms.flattenCoverRootlessRaw
    (FiniteAcceptance.trimProjection (finiteLabels P)) hP

noncomputable def innerCover {A : RankedSet} {n : ℕ} {V : Type}
    (P : Presentation (Lax369799.FinitePresentations.FiniteSystem A) n V) :
    Lax369799.PresentationCovers.Cover
      (Lax369799.FinitePresentations.flattenPresentation
        (finiteLabels (Lax369799.RootlessFlattening.trimLabels P)))
      (Lax369799.FinitePresentations.flattenPresentation P) :=
  FiniteCovers.substituteCover P
    (fun v => (trim (Lax369799.FinitePresentations.Inner P v).graph).graph)
    (fun v => (Lax369799.FinitePresentations.Inner P v).graph)
    (fun v => FiniteAcceptance.trimProjection (Lax369799.FinitePresentations.Inner P v).graph)

/--
---
conclusion: Lax369799.ObservedSubstitution.transfer_value
---
Pass to the reachable outer pattern through a cover. Transfer its resolution
using bounded profiles, then compose with the cover of the replacement pattern.
-/
theorem transfer_value {A B : RankedSet} (E : Algebra B) (hE : UnfoldInvariant E)
    [Finite (B 1)] (η : RankedMap A B) {V : Type} [Fintype V]
    (P : Presentation (SetSystem A) 0 V) (Q : ∀ v, SetSystem A (P.label v).1)
    (hP : ∀ v, (P.label v).2.graph.root = ∅) (hQ : ∀ v, (Q v).graph.root = ∅)
    (h : ∀ v, Lax369799.FiniteProfiles.BoundedProfile (Nat.card (B 1) + 1)
        (fun k R => E.eval k (relabelSystem η R)) (P.label v).2 =
      Lax369799.FiniteProfiles.BoundedProfile (Nat.card (B 1) + 1)
        (fun k R => E.eval k (relabelSystem η R)) (Q v)) :
    values E η (Lax369799.FinitePresentations.flattenPresentation (finiteLabels P)) ⊆
      values E η (Lax369799.FinitePresentations.flattenPresentation (finiteLabels (replaceLabels P Q))) := by
  intro b hb
  rw [← PresentationObservations.values_cover E hE η (outerCover P hP)] at hb
  obtain ⟨R, hR, hb⟩ := hb
  obtain ⟨U, hU, he⟩ := ProfileSubstitution.transfer_resolution E hE η (trim P)
    (fun v => Q (vertex P v)) (fun v => h (vertex P v)) R hR
  rw [← PresentationObservations.values_cover E hE η (outerCover (replaceLabels P Q) hQ)]
  exact ⟨U, hU, he.symm.trans hb⟩

end Lax369799Proofs.ObservedSubstitution
