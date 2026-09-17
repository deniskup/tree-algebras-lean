import Lax369799.BoundedProfileRefinement
import Lax369799Proofs.RootProfileSubstitution
import Lax369799Proofs.AcceptanceObservations
import Lax369799Proofs.BoundedProfiles

set_option backward.isDefEq.respectTransparency false
namespace Lax369799Proofs.BoundedProfileRefinement
open Lax369799.RankedSystems Lax369799.Algebras Lax369799.FiniteProfiles
open Lax369799.FinitePresentations Lax369799.PresentationObservations
open Lax369799.RootExpansion Lax369799.RootlessFlattening

private def replace {A : RankedSet} {n : ℕ} {V : Type}
    (P : Presentation (FiniteSystem A) n V) (Q : ∀ v, FiniteSystem A (P.label v).1) :
    Presentation (FiniteSystem A) n V := { P with label := fun v => ⟨(P.label v).1, Q v⟩ }

private theorem transfer {A B : RankedSet} (E : Algebra B) (hE : UnfoldInvariant E)
    [Finite (B 1)] (η : RankedMap A B) {V : Type} [Fintype V]
    (P : Presentation (FiniteSystem A) 0 V) (Q : ∀ v, FiniteSystem A (P.label v).1)
    (h : ∀ v, BoundedProfileEquivalent (Nat.card (B 1) + 1)
      (fun k R => E.eval k (relabelSystem η R)) (Inner P v) (Q v)) :
    (values E η (flattenPresentation P) ⊆ values E η (flattenPresentation (replace P Q))) ∧
    (values E η (startAtRoots (flattenPresentation P)) ⊆
      values E η (startAtRoots (flattenPresentation (replace P Q)))) := by
  let X := trimLabels P
  let Y := trimLabels (replace P Q)
  constructor
  · intro b hb
    rw [← PresentationObservations.values_cover E hE η (ObservedSubstitution.innerCover P)] at hb
    rw [← PresentationObservations.values_cover E hE η (ObservedSubstitution.innerCover (replace P Q))]
    exact RootProfileSubstitution.transfer_initial_value E hE η X (fun v => (Y.label v).2)
      (fun v => (h v).1) hb
  · intro b hb
    rw [← PresentationObservations.root_values_cover E hE η (ObservedSubstitution.innerCover P)] at hb
    rw [← PresentationObservations.root_values_cover E hE η (ObservedSubstitution.innerCover (replace P Q))]
    exact RootProfileSubstitution.transfer_root_value E hE η X (fun v => (Y.label v).2)
      (fun v => (h v).1) (fun v => (h v).2) hb

theorem enumerate_acceptance {A B : RankedSet} (E : Algebra B) (hE : UnfoldInvariant E)
    (η : RankedMap A B) (F : Set (B 0)) (L : Language A) (hL : Recognizes E η F L)
    {V : Type} [Fintype V] (G : Presentation A 0 V) :
    Lax369799.FiniteAcceptance.Accepting L (enumerate G) ↔
      values E η G ⊆ F ∧ values E η (startAtRoots G) ⊆ F := by
  classical
  let f : Lax369799.PresentationCovers.Cover G (enumerate G).graph := FiniteCovers.isoCover (UntrimmedFlattening.reindexIso G (Fintype.equivFin V))
  change Lax369799.SyntacticOrder.Accepting L (trim (enumerate G).graph) ↔ _
  rw [AcceptanceObservations.accepting_iff_values E hE η F L hL,
    ← PresentationObservations.values_cover E hE η f,
    ← PresentationObservations.root_values_cover E hE η f]

private theorem below {A B : RankedSet} (E : Algebra B) (hE : UnfoldInvariant E)
    [Finite (B 1)] (η : RankedMap A B) (F : Set (B 0)) (L : Language A)
    (hL : Recognizes E η F L) {n : ℕ} (S T : FiniteSystem A n)
    (h : BoundedProfileEquivalent (Nat.card (B 1) + 1)
      (fun k R => E.eval k (relabelSystem η R)) S T) :
    Lax369799.FiniteContextualOrder.Below (Lax369799.FiniteAcceptance.Accepting L) S T := by
  intro C hc
  let P := (Lax369799.FinitePresentations.relabel (Lax369799.FiniteContexts.substitution T) C.system).graph
  let Q := fun v => Lax369799.FiniteContexts.substitution S _ (C.system.graph.label v).2
  have hp : ∀ v, BoundedProfileEquivalent (Nat.card (B 1) + 1)
      (fun k R => E.eval k (relabelSystem η R)) (Inner P v) (Q v) := by
    intro v
    change BoundedProfileEquivalent _ _
      (Lax369799.FiniteContexts.substitution T _ (C.system.graph.label v).2)
      (Lax369799.FiniteContexts.substitution S _ (C.system.graph.label v).2)
    obtain ⟨k, a⟩ := C.system.graph.label v
    cases a with
    | inl a => exact ⟨rfl, rfl⟩
    | inr e => cases e with | up e => cases e; exact ⟨h.1.symm, h.2.symm⟩
  have ht := transfer E hE η P Q hp
  have hs := (enumerate_acceptance E hE η F L hL (flattenPresentation (replace P Q))).mp hc
  exact (enumerate_acceptance E hE η F L hL (flattenPresentation P)).mpr
    ⟨fun _ hb => hs.1 (ht.1 hb), fun _ hb => hs.2 (ht.2 hb)⟩

/--
---
conclusion: Lax369799.BoundedProfileRefinement.refines
---
In every context, equal bounded profiles at the hole transfer initial and
root observation values in both directions. The recognizing accepting set
therefore gives the same universal yield-acceptance test.
-/
theorem refines {A B : RankedSet} (E : Algebra B) (hE : UnfoldInvariant E)
    [Finite (B 1)] (η : RankedMap A B) (F : Set (B 0)) (L : Language A)
    (hL : Recognizes E η F L) {n : ℕ} (S T : FiniteSystem A n)
    (h : BoundedProfileEquivalent (Nat.card (B 1) + 1)
      (fun k R => E.eval k (relabelSystem η R)) S T) :
    Lax369799.FiniteContextualOrder.Equivalent (Lax369799.FiniteAcceptance.Accepting L) S T :=
  ⟨below E hE η F L hL S T h, below E hE η F L hL T S ⟨h.1.symm, h.2.symm⟩⟩

/--
---
conclusion: Lax369799.BoundedProfileRefinement.finite_carrier
---
The finite bounded-profile quotient maps onto the contextual quotient,
because profile equality refines contextual equivalence in every rank.
-/
theorem finite_carrier {A : RankedSet} (L : Language A) (hL : RegularTreeRecognizable L) :
    RankwiseFinite (Lax369799.FiniteContextualOrder.Carrier (Lax369799.FiniteAcceptance.Accepting L)) := by
  obtain ⟨B, E, η, F, hB, hE, hL⟩ := hL
  let : Finite (B 1) := hB 1
  intro n
  let ρ := fun k R => E.eval k (relabelSystem η R)
  let := BoundedProfiles.bounded_profile_finite hB (Nat.card (B 1) + 1) ρ n
  let f : Quot (@BoundedProfileEquivalent A B (Nat.card (B 1) + 1) ρ n) →
      Lax369799.FiniteContextualOrder.Carrier (Lax369799.FiniteAcceptance.Accepting L) n :=
    Quot.lift (fun S => Quot.mk _ S) (fun S T h => Quot.sound (refines E hE η F L hL S T h))
  apply Finite.of_surjective f
  intro x
  induction x using Quot.inductionOn with
  | h S => exact ⟨Quot.mk _ S, rfl⟩

end Lax369799Proofs.BoundedProfileRefinement
