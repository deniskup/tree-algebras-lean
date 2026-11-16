import Lax369799Proofs.SupportedProfiles
import Lax369799Proofs.UnboundedSubstitution
import Lax369799Proofs.FiniteRenaming

set_option backward.isDefEq.respectTransparency false
namespace Lax369799Proofs.SupportedProfiles
open Lax369799
open RankedSystems FinitePresentations
open SupportedMorphisms FiniteRenaming
open SupportEvaluation (Carrier classMap)

private theorem reflect_supported {A B : RankedSet} (E : SupportedAlgebras.Algebra B)
    (η : RankedMap A B) {m : ℕ} (W : System A m) (U : SupportedSystems.System A m)
    (h : classMap E m (relabelSystem η W) = classMap E m (relabelSystem η U.val)) :
    ∃ V : SupportedSystems.System A m, V.val = W ∧
      E.eval m (SupportedSystems.relabel η V) = E.eval m (SupportedSystems.relabel η U) := by
  let r : Setoid (System B m) := {
    r := SupportEvaluation.Equivalent E
    iseqv := ⟨fun _ => rfl,Eq.symm,Eq.trans⟩ }
  have hp : SupportEvaluation.Equivalent E (relabelSystem η W) (relabelSystem η U.val) :=
    @Quotient.exact _ r _ _ h
  let o : SupportEvaluation.Observation B m :=
    ⟨⟨m,Nat.lt_succ_self m⟩,Function.Embedding.refl _,E.eval m (SupportedSystems.relabel η U)⟩
  have ho : o ∈ SupportEvaluation.profile E (relabelSystem η U.val) :=
    ⟨SupportedSystems.relabel η U,Subtype.ext (Renaming.rename_identity _),rfl⟩
  rw [←hp] at ho
  obtain ⟨V,hV,hvalue⟩ := ho
  have hV' : V.val = relabelSystem η W :=
    (Subtype.ext (Renaming.rename_identity V.val.val)).symm.trans hV
  have hs : SupportedSystems.FullySupported W := by
    change SupportedSystems.FullySupported (relabelSystem η W)
    rw [←hV']; exact V.property
  let W' : SupportedSystems.System A m := ⟨W,hs⟩
  have he : SupportedSystems.relabel η W' = V := Subtype.ext hV'.symm
  exact ⟨W',rfl,(congrArg (E.eval m) he).trans hvalue⟩

private theorem profiles_of_pull_values {A B : RankedSet} (E : SupportedAlgebras.Algebra B)
    (η : RankedMap A B) (D : Algebras.Algebra (Carrier E))
    (hD : ∀ n (R : System B n),
      D.eval n (relabelSystem (SupportedCompletion.letter E) R) = classMap E n R)
    {n : ℕ} (S T : FiniteSystem A n)
    (h : ∀ m (σ : Fin m → Fin n),
      PresentationObservations.values D (fun j a => SupportedCompletion.letter E j (η j a)) (pull σ S).graph =
        PresentationObservations.values D (fun j a => SupportedCompletion.letter E j (η j a)) (pull σ T).graph) :
    Lax369799.SupportedProfiles.Profile E η S = Lax369799.SupportedProfiles.Profile E η T := by
  let κ : RankedMap A (Carrier E) := fun j a => SupportedCompletion.letter E j (η j a)
  have forward (S T : FiniteSystem A n)
      (h : ∀ m (σ : Fin m → Fin n),
        PresentationObservations.values D κ (pull σ S).graph =
          PresentationObservations.values D κ (pull σ T).graph) :
      Lax369799.SupportedProfiles.Profile E η S ⊆ Lax369799.SupportedProfiles.Profile E η T := by
    rintro ⟨m,b,σ⟩ ⟨U,⟨a⟩,ha⟩
    obtain ⟨a',_⟩ := (FiniteRenaming.adjunction σ (presentation U) S a.toFun).mp ⟨a,rfl⟩
    have hv : D.eval m (relabelSystem κ U.val) ∈ PresentationObservations.values D κ (pull σ S).graph :=
      (PresentationObservations.values_iff_map D κ _ _).mpr
        ⟨U.val,⟨⟨a'.toFun,a'.initial,a'.root,a'.label,a'.edge⟩⟩,rfl⟩
    rw [h] at hv
    obtain ⟨W,⟨w⟩,hw⟩ := (PresentationObservations.values_iff_map D κ _ _).mp hv
    have hc : classMap E m (relabelSystem η W) = classMap E m (relabelSystem η U.val) :=
      (hD m (relabelSystem η W)).symm.trans (hw.trans (hD m (relabelSystem η U.val)))
    obtain ⟨V,hV,hvalue⟩ := reflect_supported E η W U hc
    let v : FiniteMorphisms.Morphism (presentation V) (pull σ T) := by
      rw [show presentation V = ofSetSystem W.val from congrArg ofSetSystem (congrArg Subtype.val hV)]
      exact ⟨w.toFun,w.initial,w.root,w.label,w.edge⟩
    obtain ⟨v',_⟩ := (FiniteRenaming.adjunction σ (presentation V) T v.toFun).mpr ⟨v,rfl⟩
    exact ⟨V,⟨v'⟩,hvalue.trans ha⟩
  exact Set.Subset.antisymm (forward S T h) (forward T S (fun m σ => (h m σ).symm))

private theorem unbounded_values {A B : RankedSet} (D : Algebras.Algebra B)
    (hD : Algebras.UnfoldInvariant D) (η : RankedMap A B) {n : ℕ} {V : Type} [Fintype V]
    (P : Presentation (FiniteSystem A) n V) (Q : ∀ v, FiniteSystem A (P.label v).1)
    (h : ∀ v, Resolutions.ProfileEquivalent (fun k R => D.eval k (relabelSystem η R)) (trim (Inner P v).graph) (trim (Q v).graph)) :
    (PresentationObservations.values D η (flattenPresentation P) ⊆
      PresentationObservations.values D η (flattenPresentation (BoundedProfileRefinement.replace P Q))) ∧
    (PresentationObservations.values D η (RootExpansion.startAtRoots (flattenPresentation P)) ⊆
      PresentationObservations.values D η (RootExpansion.startAtRoots (flattenPresentation (BoundedProfileRefinement.replace P Q)))) := by
  let X := RootlessFlattening.trimLabels P
  let Y := RootlessFlattening.trimLabels (BoundedProfileRefinement.replace P Q)
  constructor
  · intro b hb
    rw [←PresentationObservations.values_cover D hD η (ObservedSubstitution.innerCover P)] at hb
    rw [←PresentationObservations.values_cover D hD η (ObservedSubstitution.innerCover (BoundedProfileRefinement.replace P Q))]
    exact UnboundedSubstitution.transfer_initial_value D hD η X (fun v => (Y.label v).2) (fun v => (h v).1) hb
  · intro b hb
    rw [←PresentationObservations.root_values_cover D hD η (ObservedSubstitution.innerCover P)] at hb
    rw [←PresentationObservations.root_values_cover D hD η (ObservedSubstitution.innerCover (BoundedProfileRefinement.replace P Q))]
    exact UnboundedSubstitution.transfer_root_value D hD η X (fun v => (Y.label v).2) (fun v => (h v).1) (fun v => (h v).2) hb

/--
---
conclusion: Lax369799.SupportedProfiles.congruence
---
Move each output map across the resolution using inverse renaming, which
commutes with flattening. Transfer full initial and root observations in
the unfolding-invariant completion. Equal completed values restore full
support and the original supported values (Lemma 78).
-/
theorem congruence {A B : RankedSet} (E : SupportedAlgebras.Algebra B)
    (hE : SupportedAlgebras.UnfoldInvariant E) (η : RankedMap A B) {n : ℕ}
    (P : FiniteSystem (FiniteSystem A) n) (Q : ∀ v, FiniteSystem A (P.graph.label v).1)
    (h : ∀ v, Lax369799.SupportedProfiles.ProfileEquivalent E η (Inner P.graph v) (Q v)) :
    Lax369799.SupportedProfiles.ProfileEquivalent E η (flatten P) (flatten (withLabels P Q)) := by
  classical
  obtain ⟨D,hDE,hD⟩ := SupportedCompletion.regular_completion E hE
  let κ : RankedMap A (Carrier E) := fun j a => SupportedCompletion.letter E j (η j a)
  let R := withLabels P Q
  have hp (v : P.Vertex) := full_completion E η D hDE hD (Inner P.graph v) (Q v) (h v)
  have pull_values (m : ℕ) (σ : Fin m → Fin n) :
      (PresentationObservations.values D κ (pull σ (flatten P)).graph =
        PresentationObservations.values D κ (pull σ (flatten R)).graph) ∧
      (PresentationObservations.values D κ (pull σ (SupportedYields.uproot (flatten P))).graph =
        PresentationObservations.values D κ (pull σ (SupportedYields.uproot (flatten R))).graph) := by
    let X := pull σ P
    let Y := pull σ R
    have hf := unbounded_values D hDE κ X.graph Q hp
    have hr (v : Y.Vertex) : Resolutions.ProfileEquivalent (fun k S => D.eval k (relabelSystem κ S))
        (trim (Inner Y.graph v).graph) (trim (Inner P.graph v).graph) := ⟨(hp v).1.symm,(hp v).2.symm⟩
    have hb := unbounded_values D hDE κ Y.graph (fun v => Inner P.graph v) hr
    have hrestore : BoundedProfileRefinement.replace Y.graph (fun v => Inner P.graph v) = X.graph := by
      cases P; rfl
    rw [hrestore] at hb
    let G := flattenPresentation X.graph
    let H := flattenPresentation Y.graph
    have hi : PresentationObservations.values D κ G = PresentationObservations.values D κ H :=
      Set.Subset.antisymm hf.1 hb.1
    have hroot : PresentationObservations.values D κ (RootExpansion.startAtRoots G) =
        PresentationObservations.values D κ (RootExpansion.startAtRoots H) := Set.Subset.antisymm hf.2 hb.2
    let cG := FiniteCovers.isoCover (UntrimmedFlattening.reindexIso G (Fintype.equivFin _))
    let cH := FiniteCovers.isoCover (UntrimmedFlattening.reindexIso H (Fintype.equivFin _))
    have gi := congrArg (fun Z : FiniteSystem A m => PresentationObservations.values D κ Z.graph)
      (FiniteRenaming.pull_flatten σ P)
    have hi' := congrArg (fun Z : FiniteSystem A m => PresentationObservations.values D κ Z.graph)
      (FiniteRenaming.pull_flatten σ R)
    have gr := congrArg (fun Z : FiniteSystem A m => PresentationObservations.values D κ (RootExpansion.startAtRoots Z.graph))
      (FiniteRenaming.pull_flatten σ P)
    have hr' := congrArg (fun Z : FiniteSystem A m => PresentationObservations.values D κ (RootExpansion.startAtRoots Z.graph))
      (FiniteRenaming.pull_flatten σ R)
    constructor
    · exact gi.trans ((PresentationObservations.values_cover D hDE κ cG).symm.trans
        (hi.trans ((PresentationObservations.values_cover D hDE κ cH).trans hi'.symm)))
    · exact gr.trans ((PresentationObservations.root_values_cover D hDE κ cG).symm.trans
        (hroot.trans ((PresentationObservations.root_values_cover D hDE κ cH).trans hr'.symm)))
  exact ⟨profiles_of_pull_values E η D hD _ _ (fun m σ => (pull_values m σ).1),
    profiles_of_pull_values E η D hD _ _ (fun m σ => (pull_values m σ).2)⟩

end Lax369799Proofs.SupportedProfiles
