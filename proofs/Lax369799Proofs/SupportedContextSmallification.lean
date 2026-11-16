import Lax369799.SupportedContextSmallification
import Lax369799Proofs.SupportedCompletionProperties
import Lax369799Proofs.ContinuationCompression
import Lax369799Proofs.ContextPorts

set_option backward.isDefEq.respectTransparency false
namespace Lax369799Proofs.SupportedContextSmallification
open Lax369799
open RankedSystems Morphisms Flattening

private theorem rewiring {A B : RankedSet} (E : SupportedAlgebras.Algebra B)
    (hB : RankwiseFinite B) (hE : SupportedAlgebras.UnfoldInvariant E) (η : RankedMap A B)
    {m n : ℕ} (C : SetContext A m 0) (hC : C.system.Deterministic)
    (S : SupportedSystems.System A m) (σ : Fin m → Fin n) :
    ∃ (m' : ℕ) (τ : Fin m → Fin m') (sectionMap : Fin m' → Fin m),
      m' ≤ m ∧ Function.Surjective τ ∧ Function.Injective sectionMap ∧
      (∀ j,τ (sectionMap j) = j) ∧ (∀ i,σ (sectionMap (τ i)) = σ i) ∧
      Resolutions.SmallMap B (σ ∘ sectionMap) ∧
      ∃ U V : SupportedSystems.System A 0,
        U.val.val = plug C S.val.val ∧
        V.val.val = plug C (Renaming.renameSystem (sectionMap ∘ τ) S.val).val ∧
        E.eval 0 (SupportedSystems.relabel η U) = E.eval 0 (SupportedSystems.relabel η V) := by
  obtain ⟨D,hDE,hD⟩ := SupportedCompletion.regular_completion E hE
  let : Finite (SupportEvaluation.Carrier E 1) := SupportEvaluation.finite_carrier E hB 1
  let κ : RankedMap A (SupportEvaluation.Carrier E) := fun j a => SupportedCompletion.letter E j (η j a)
  obtain ⟨m',τ,s,hs,hσ,hb,U,V,hU,hV,he⟩ :=
    ContinuationCompression.mapped_context_smallification D hDE κ C hC S.val σ
  have hsurj : Function.Surjective τ := fun j => ⟨s j,hs j⟩
  have hinj : Function.Injective s := by
    intro i j h
    have he := congrArg τ h
    simpa only [hs] using he
  have hm : m' ≤ m := by simpa using Fintype.card_le_of_injective s hinj
  have hsmall : Resolutions.SmallMap B (σ ∘ s) := by
    intro j
    have hj := hb j
    have hn := SupportedCompletion.unary_card_bound E hB
    unfold Resolutions.SmallBound
    change Nat.card {i // σ (s i) = j} ≤ _
    omega
  obtain ⟨e,hee⟩ := SupportEvaluation.closed_carrier E
  have hc : SupportEvaluation.classMap E 0 (relabelSystem η U) =
      SupportEvaluation.classMap E 0 (relabelSystem η V) :=
    (hD 0 (relabelSystem η U)).symm.trans (he.trans (hD 0 (relabelSystem η V)))
  refine ⟨m',τ,s,hm,hsurj,hinj,hs,hσ,hsmall,
    (SupportedSystems.closedEquiv A).symm U,(SupportedSystems.closedEquiv A).symm V,hU,hV,?_⟩
  exact (hee (relabelSystem η U)).symm.trans ((congrArg e hc).trans (hee (relabelSystem η V)))


/--
---
conclusion: Lax369799.SupportedContextSmallification.smallification
---
Compress the completed unary observations, whose cardinality is bounded
by |B₀| + |B₁|. Resize the hole to the quotient arity and select the
representative successor in every new direction. The port-substitution
isomorphism proves equality with the original closed evaluation (Lemma 81).
-/
theorem smallification {A B : RankedSet} (E : SupportedAlgebras.Algebra B)
    (hB : RankwiseFinite B) (hE : SupportedAlgebras.UnfoldInvariant E) (η : RankedMap A B)
    {m n : ℕ} (C : SetContext A m 0) (hC : C.system.Deterministic)
    (S : SupportedSystems.System A m) (σ : Fin m → Fin n) :
    ∃ (m' : ℕ) (τ : Fin m → Fin m') (sectionMap : Fin m' → Fin m),
      m' ≤ m ∧ Function.Surjective τ ∧ Function.Injective sectionMap ∧
      (∀ j,τ (sectionMap j) = j) ∧ (∀ i,σ (sectionMap (τ i)) = σ i) ∧
      Resolutions.SmallMap B (σ ∘ sectionMap) ∧
      ∃ (S' : SupportedSystems.System A m') (D : SetContext A m' 0),
        S'.val = Renaming.renameSystem τ S.val ∧
        D.system = trim (Lax369799.ContextPorts.resizeGraph C sectionMap) ∧ D.system.Deterministic ∧
        ∃ U V : SupportedSystems.System A 0,
          U.val.val = plug C S.val.val ∧ V.val.val = plug D S'.val.val ∧
          E.eval 0 (SupportedSystems.relabel η U) = E.eval 0 (SupportedSystems.relabel η V) := by
  obtain ⟨m',τ,s,hm,hsurj,hinj,hs,hσ,hsmall,U,V,hU,hV,he⟩ := rewiring E hB hE η C hC S σ
  let S' := SupportedSystems.rename τ hsurj S
  obtain ⟨D,hD,hDdet⟩ := ContextPorts.resize_exists C hC s
  obtain ⟨W,hW⟩ := ContextRelabelling.plug_system D hDdet S'.val
  let W' := (SupportedSystems.closedEquiv A).symm W
  have hr : Renaming.renameSystem s S'.val = Renaming.renameSystem (s ∘ τ) S.val :=
    Subtype.ext (Renaming.rename_composition τ s S.val.val)
  have hv : V.val.val = plug C (Renaming.renameSystem s S'.val).val := by rw [hr]; exact hV
  obtain ⟨f,hf,hfc⟩ := ContextPorts.plug_resize C hC s S'.val D hD V.val W hv hW
  have hvalue := E.isomorphic 0 (SupportedSystems.relabel η V) (SupportedSystems.relabel η W')
    ⟨SystemSubstitution.relabelMorphism η f,hf,hfc⟩
  exact ⟨m',τ,s,hm,hsurj,hinj,hs,hσ,hsmall,S',D,rfl,hD,hDdet,U,W',hU,hW,he.trans hvalue⟩

end Lax369799Proofs.SupportedContextSmallification
