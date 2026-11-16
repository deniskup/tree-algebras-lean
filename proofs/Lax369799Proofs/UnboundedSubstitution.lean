import Lax369799.UnboundedSubstitution
import Lax369799Proofs.ProfileSubstitution
import Lax369799Proofs.RootProfileSubstitution

set_option backward.isDefEq.respectTransparency false
namespace Lax369799Proofs.UnboundedSubstitution
open Lax369799
open RankedSystems Morphisms Algebras
open Flattening Resolutions ProfileSubstitution
open ObservedSubstitution PresentationObservations RootExpansion RootlessFlattening
open Lax369799Proofs.Pullbacks (vertex)
open Lax369799Proofs.RootProfileSubstitution (initialPattern initialCover)

private theorem same_evaluated_labels {A B : RankedSet} {n : ℕ} (T : System (System A) n)
    (ρ : ∀ k, System A k → B k) (f : ∀ v, System A (T.val.graph.label v).1)
    (hf : ∀ v, ρ _ (f v) = ρ _ (T.val.graph.label v).2) :
    relabel ρ (withLabels T.val f) = relabel ρ T.val := by
  have hl : (relabel ρ (withLabels T.val f)).graph.label = (relabel ρ T.val).graph.label := by
    funext v
    exact congrArg (Sigma.mk _) (hf v)
  cases T with
  | mk T hT =>
    cases T with
    | mk size G hr =>
      cases G
      dsimp only [withLabels, relabel] at hl ⊢
      congr 1
      congr 1

/--
---
conclusion: Lax369799.UnboundedSubstitution.transfer_resolution
---
Factor the resolution and replace its local resolutions by equal-profile
witnesses, keeping every variable map. Associativity identifies the
flattened values in every output rank.
-/
theorem transfer_resolution {A B : RankedSet} (E : Algebra B) (hE : UnfoldInvariant E)
    (η : RankedMap A B) {n : ℕ} (P : SetSystem (SetSystem A) n)
    (Q : ∀ v, SetSystem A (P.graph.label v).1)
    (hQ : ∀ v, Profile
        (fun k R => E.eval k (relabelSystem η R)) (Inner P v) =
      Profile
        (fun k R => E.eval k (relabelSystem η R)) (Q v))
    (R : System A n) (hR : DirectResolution (flatten P) R) :
    ∃ U : System A n, DirectResolution (flatten (withLabels P Q)) U ∧
      E.eval n (relabelSystem η R) = E.eval n (relabelSystem η U) := by
  classical
  let ρ := fun k R => E.eval k (relabelSystem η R)
  obtain ⟨T, V, ⟨r⟩, hV, f, hf⟩ := ResolutionFactorization.resolution_to_flatten_resolution P R hR
  have chosen (v : T.val.Vertex) :
      ∃ W : System A (T.val.graph.label v).1,
        IsResolution (Q (r.vertex v)) W (r.variableMap v) ∧
        ρ _ W = ρ _ (T.val.graph.label v).2 := by
    let e : ProfileEntry B (P.graph.label (r.vertex v)).1 :=
      ⟨(T.val.graph.label v).1, ρ _ (T.val.graph.label v).2, r.variableMap v⟩
    have hh : e ∈ Profile ρ
        (Inner P (r.vertex v)) := ⟨(T.val.graph.label v).2, r.resolves v, rfl⟩
    rw [hQ] at hh
    exact hh
  let label' := fun v => Classical.choose (chosen v)
  have hr (v) := (Classical.choose_spec (chosen v)).1
  have heval (v) := (Classical.choose_spec (chosen v)).2
  let T' : System (System A) n := ⟨withLabels T.val label', T.property⟩
  let r' : FlattenResolution (withLabels P Q) T' := {
    vertex := r.vertex
    variableMap := r.variableMap
    initial := r.initial
    resolves := hr
    transition := r.transition
    exit := r.exit }
  obtain ⟨U, hU⟩ := Flattening.flatten_system T'
  refine ⟨U, Flattening.flatten_resolution_sound _ T' r' U hU, ?_⟩
  have hlabels : relabelSystem ρ T' = relabelSystem ρ T :=
    Subtype.ext (same_evaluated_labels T ρ label' heval)
  have flat (W : System (System A) n) (X : System A n) (hX : SystemFlattening W X) :
      E.eval n (relabelSystem ρ W) = ρ n X := by
    let WB := relabelSystem (fun _ X => relabelSystem η X) W
    have hh : SystemFlattening WB (relabelSystem η X) := by
      change relabel η X.val = _
      rw [hX]
      rfl
    exact E.associative n WB (relabelSystem η X) hh
  calc
    ρ n R = ρ n V := (ProfileSubstitution.value_morphism E hE η V R f).symm
    _ = E.eval n (relabelSystem ρ T) := (flat T V hV).symm
    _ = E.eval n (relabelSystem ρ T') := congrArg (E.eval n) hlabels.symm
    _ = ρ n U := flat T' U hU

/--
---
conclusion: Lax369799.UnboundedSubstitution.transfer_value
---
Restrict a root-free outer presentation and its labels through their
canonical covers. Transfer the resolution, then restore the original
presentation, retaining observations in every output rank.
-/
theorem transfer_value {A B : RankedSet} (E : Algebra B) (hE : UnfoldInvariant E)
    (η : RankedMap A B) {n : ℕ} {V : Type} [Fintype V]
    (P : Presentation (SetSystem A) n V) (Q : ∀ v, SetSystem A (P.label v).1)
    (hP : ∀ v, (P.label v).2.graph.root = ∅) (hQ : ∀ v, (Q v).graph.root = ∅)
    (h : ∀ v, Profile
        (fun k R => E.eval k (relabelSystem η R)) (P.label v).2 =
      Profile
        (fun k R => E.eval k (relabelSystem η R)) (Q v)) :
    values E η (Lax369799.FinitePresentations.flattenPresentation (finiteLabels P)) ⊆
      values E η (Lax369799.FinitePresentations.flattenPresentation (finiteLabels (replaceLabels P Q))) := by
  intro b hb
  rw [← PresentationObservations.values_cover E hE η (outerCover P hP)] at hb
  obtain ⟨R, hR, hb⟩ := hb
  obtain ⟨U, hU, he⟩ := UnboundedSubstitution.transfer_resolution E hE η (trim P)
    (fun v => Q (vertex P v)) (fun v => h (vertex P v)) R hR
  rw [← PresentationObservations.values_cover E hE η (outerCover (replaceLabels P Q) hQ)]
  exact ⟨U, hU, he.symm.trans hb⟩

/--
---
conclusion: Lax369799.UnboundedSubstitution.transfer_initial_value
---
Remove root marks, transfer full initial profiles, and restore the marks.
The argument applies to arbitrary finite outer presentations and all ranks.
-/
theorem transfer_initial_value {A B : RankedSet} (E : Algebra B) (hE : UnfoldInvariant E)
    (η : RankedMap A B) {n : ℕ} {V : Type} [Fintype V]
    (P : Presentation (SetSystem A) n V) (Q : ∀ v, SetSystem A (P.label v).1)
    (hi : ∀ v, Profile
        (fun k R => E.eval k (relabelSystem η R)) (P.label v).2 =
      Profile
        (fun k R => E.eval k (relabelSystem η R)) (Q v)) :
    values E η (Lax369799.FinitePresentations.flattenPresentation (finiteLabels P)) ⊆
      values E η (Lax369799.FinitePresentations.flattenPresentation (finiteLabels (replaceLabels P Q))) := by
  let X := initialPattern P
  let Y := initialPattern (replaceLabels P Q)
  let PX := trimLabels X
  let PY := trimLabels Y
  have hx : ∀ v, (PX.label v).2.graph.root = ∅ := by intro v; ext w; rfl
  have hy : ∀ v, (PY.label v).2.graph.root = ∅ := by intro v; ext w; rfl
  have hp : ∀ v, Profile
      (fun k R => E.eval k (relabelSystem η R)) (PX.label v).2 =
    Profile
      (fun k R => E.eval k (relabelSystem η R)) (PY.label v).2 := by
    intro v
    change Profile _ (Lax369799.RootObservations.initialPart (P.label v).2) =
      Profile _ (Lax369799.RootObservations.initialPart (Q v))
    rw [RootObservations.initial_profile,RootObservations.initial_profile]
    exact hi v
  intro b hb
  rw [← PresentationObservations.values_remove_roots E η,
    ← PresentationObservations.values_cover E hE η (initialCover P),
    ← PresentationObservations.values_cover E hE η (ObservedSubstitution.innerCover X)] at hb
  have hb' := UnboundedSubstitution.transfer_value E hE η PX (fun v => (PY.label v).2) hx hy hp hb
  rw [← PresentationObservations.values_remove_roots E η,
    ← PresentationObservations.values_cover E hE η (initialCover (replaceLabels P Q)),
    ← PresentationObservations.values_cover E hE η (ObservedSubstitution.innerCover Y)]
  exact hb'


/--
---
conclusion: Lax369799.UnboundedSubstitution.transfer_root_value
---
Separate root-starting and ordinary copies of every component, transfer
their full profiles, then forget the copy flags through the expansion cover.
-/
theorem transfer_root_value {A B : RankedSet} (E : Algebra B) (hE : UnfoldInvariant E)
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
        (finiteLabels (replaceLabels P Q)))) := by
  let X := pattern (finiteLabels P)
  let Y := pattern (finiteLabels (replaceLabels P Q))
  let PX := trimLabels X
  let PY := trimLabels Y
  have hx : ∀ v, (PX.label v).2.graph.root = ∅ := by intro v; ext w; rfl
  have hy : ∀ v, (PY.label v).2.graph.root = ∅ := by intro v; ext w; rfl
  have hp : ∀ v, Profile
      (fun k R => E.eval k (relabelSystem η R)) (PX.label v).2 =
    Profile
      (fun k R => E.eval k (relabelSystem η R)) (PY.label v).2 := by
    rintro ⟨b, v⟩
    cases b with
    | false =>
      change Profile _ (Lax369799.RootObservations.initialPart (P.label v).2) =
        Profile _ (Lax369799.RootObservations.initialPart (Q v))
      rw [RootObservations.initial_profile,RootObservations.initial_profile]
      exact hi v
    | true => exact hr v
  intro b hb
  rw [← PresentationObservations.values_cover E hE η (RootExpansion.expansionCover (finiteLabels P)),
    ← PresentationObservations.values_cover E hE η (ObservedSubstitution.innerCover X)] at hb
  have hb' := UnboundedSubstitution.transfer_value E hE η PX (fun v => (PY.label v).2) hx hy hp hb
  rw [← PresentationObservations.values_cover E hE η
      (RootExpansion.expansionCover (finiteLabels (replaceLabels P Q))),
    ← PresentationObservations.values_cover E hE η (ObservedSubstitution.innerCover Y)]
  exact hb'

end Lax369799Proofs.UnboundedSubstitution
