import Lax369799.RootProfileSubstitution
import Lax369799Proofs.ObservedSubstitution
import Lax369799Proofs.RootExpansion
import Lax369799Proofs.RootObservations

set_option backward.isDefEq.respectTransparency false
namespace Lax369799Proofs.RootProfileSubstitution
open Lax369799.RankedSystems Lax369799.Algebras Lax369799.ObservedSubstitution
open Lax369799.PresentationObservations Lax369799.FiniteProfiles
open Lax369799.RootExpansion Lax369799.RootlessFlattening

private theorem bounded_initial {A B : RankedSet} (bound : ℕ)
    (ρ : ∀ k, System A k → B k) {n : ℕ} (S : SetSystem A n) :
    BoundedProfile bound ρ (Lax369799.RootObservations.initialPart S) = BoundedProfile bound ρ S := by
  unfold BoundedProfile
  rw [RootObservations.initial_profile]

private def initialPattern {A : RankedSet} {n : ℕ} {V : Type}
    (P : Presentation (SetSystem A) n V) :
    Presentation (Lax369799.FinitePresentations.FiniteSystem A) n V := {
  finiteLabels P with
    label := fun v => ⟨(P.label v).1, component (Lax369799.FinitePresentations.ofSetSystem (P.label v).2) false⟩
    root := ∅ }

private def initialCover {A : RankedSet} {n : ℕ} {V : Type}
    (P : Presentation (SetSystem A) n V) :
    Lax369799.PresentationCovers.Cover
      (Lax369799.FinitePresentations.flattenPresentation (initialPattern P))
      { Lax369799.FinitePresentations.flattenPresentation (finiteLabels P) with root := ∅ } where
  toFun := id
  label := fun _ => rfl
  initial := fun _ h => h
  root := by rintro v (h | ⟨h, _⟩) <;> exact False.elim h
  edge := by
    intro v d t h
    change (Lax369799.FinitePresentations.flattenPresentation (finiteLabels P)).edge v d t at h
    simpa only [Sum.map_id_id, id_eq] using h
  initial_lift := fun v h => ⟨v, h, rfl⟩
  root_lift := fun _ h => False.elim h
  edge_lift := fun _ _ t h => ⟨t, h, by simp only [Sum.map_id_id, id_eq]⟩

/--
---
conclusion: Lax369799.RootProfileSubstitution.transfer_initial_value
---
Remove root marks and restrict the inner components to their initial parts.
Their initial profiles are unchanged. Transfer the resulting root-free
observation and then restore the original marks.
-/
theorem transfer_initial_value {A B : RankedSet} (E : Algebra B) (hE : UnfoldInvariant E)
    [Finite (B 1)] (η : RankedMap A B) {V : Type} [Fintype V]
    (P : Presentation (SetSystem A) 0 V) (Q : ∀ v, SetSystem A (P.label v).1)
    (hi : ∀ v, BoundedProfile (Nat.card (B 1) + 1)
        (fun k R => E.eval k (relabelSystem η R)) (P.label v).2 =
      BoundedProfile (Nat.card (B 1) + 1)
        (fun k R => E.eval k (relabelSystem η R)) (Q v)) :
    values E η (Lax369799.FinitePresentations.flattenPresentation (finiteLabels P)) ⊆
      values E η (Lax369799.FinitePresentations.flattenPresentation (finiteLabels (replaceLabels P Q))) := by
  let X := initialPattern P
  let Y := initialPattern (replaceLabels P Q)
  let PX := trimLabels X
  let PY := trimLabels Y
  have hx : ∀ v, (PX.label v).2.graph.root = ∅ := by intro v; ext w; rfl
  have hy : ∀ v, (PY.label v).2.graph.root = ∅ := by intro v; ext w; rfl
  have hp : ∀ v, BoundedProfile (Nat.card (B 1) + 1)
      (fun k R => E.eval k (relabelSystem η R)) (PX.label v).2 =
    BoundedProfile (Nat.card (B 1) + 1)
      (fun k R => E.eval k (relabelSystem η R)) (PY.label v).2 := by
    intro v
    change BoundedProfile _ _ (Lax369799.RootObservations.initialPart (P.label v).2) =
      BoundedProfile _ _ (Lax369799.RootObservations.initialPart (Q v))
    rw [bounded_initial, bounded_initial]
    exact hi v
  intro b hb
  rw [← PresentationObservations.values_remove_roots E η,
    ← PresentationObservations.values_cover E hE η (initialCover P),
    ← PresentationObservations.values_cover E hE η (ObservedSubstitution.innerCover X)] at hb
  have hb' := ObservedSubstitution.transfer_value E hE η PX (fun v => (PY.label v).2) hx hy hp hb
  rw [← PresentationObservations.values_remove_roots E η,
    ← PresentationObservations.values_cover E hE η (initialCover (replaceLabels P Q)),
    ← PresentationObservations.values_cover E hE η (ObservedSubstitution.innerCover Y)]
  exact hb'

/--
---
conclusion: Lax369799.RootProfileSubstitution.transfer_root_value
---
Expand every possible root entry into a separate starting copy. Its inner
profile is the root profile, while ordinary copies use initial profiles.
Restrict these root-free components, transfer their bounded observations,
and forget the starting-copy flags through the expansion cover.
-/
theorem transfer_root_value {A B : RankedSet} (E : Algebra B) (hE : UnfoldInvariant E)
    [Finite (B 1)] (η : RankedMap A B) {V : Type} [Fintype V]
    (P : Presentation (SetSystem A) 0 V) (Q : ∀ v, SetSystem A (P.label v).1)
    (hi : ∀ v, BoundedProfile (Nat.card (B 1) + 1)
        (fun k R => E.eval k (relabelSystem η R)) (P.label v).2 =
      BoundedProfile (Nat.card (B 1) + 1)
        (fun k R => E.eval k (relabelSystem η R)) (Q v))
    (hr : ∀ v, BoundedProfile (Nat.card (B 1) + 1)
        (fun k R => E.eval k (relabelSystem η R)) (uproot (P.label v).2) =
      BoundedProfile (Nat.card (B 1) + 1)
        (fun k R => E.eval k (relabelSystem η R)) (uproot (Q v))) :
    values E η (startAtRoots (Lax369799.FinitePresentations.flattenPresentation (finiteLabels P))) ⊆
      values E η (startAtRoots (Lax369799.FinitePresentations.flattenPresentation
        (finiteLabels (replaceLabels P Q)))) := by
  let X := pattern (finiteLabels P)
  let Y := pattern (finiteLabels (replaceLabels P Q))
  let PX := trimLabels X
  let PY := trimLabels Y
  have hx : ∀ v, (PX.label v).2.graph.root = ∅ := by intro v; ext w; rfl
  have hy : ∀ v, (PY.label v).2.graph.root = ∅ := by intro v; ext w; rfl
  have hp : ∀ v, BoundedProfile (Nat.card (B 1) + 1)
      (fun k R => E.eval k (relabelSystem η R)) (PX.label v).2 =
    BoundedProfile (Nat.card (B 1) + 1)
      (fun k R => E.eval k (relabelSystem η R)) (PY.label v).2 := by
    rintro ⟨b, v⟩
    cases b with
    | false =>
      change BoundedProfile _ _ (Lax369799.RootObservations.initialPart (P.label v).2) =
        BoundedProfile _ _ (Lax369799.RootObservations.initialPart (Q v))
      rw [bounded_initial, bounded_initial]
      exact hi v
    | true => exact hr v
  intro b hb
  rw [← PresentationObservations.values_cover E hE η (RootExpansion.expansionCover (finiteLabels P)),
    ← PresentationObservations.values_cover E hE η (ObservedSubstitution.innerCover X)] at hb
  have hb' := ObservedSubstitution.transfer_value E hE η PX (fun v => (PY.label v).2) hx hy hp hb
  rw [← PresentationObservations.values_cover E hE η
      (RootExpansion.expansionCover (finiteLabels (replaceLabels P Q))),
    ← PresentationObservations.values_cover E hE η (ObservedSubstitution.innerCover Y)]
  exact hb'

end Lax369799Proofs.RootProfileSubstitution
