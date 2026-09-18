import Lax369799.YieldSubstitution
import Lax369799Proofs.ResolutionLifting
import Lax369799Proofs.ResolutionFactorization
import Lax369799Proofs.SystemSubstitution

set_option backward.isDefEq.respectTransparency false
namespace Lax369799Proofs.YieldSubstitution
open Lax369799.RankedSystems Lax369799.Morphisms Lax369799.Flattening
open Lax369799.Resolutions Lax369799.ProfileSubstitution

theorem transfer_initial_resolution {A : RankedSet} {n : ℕ}
    (P : SetSystem (SetSystem A) n) (Q : ∀ v, SetSystem A (P.graph.label v).1)
    (hQ : ∀ v U, InitYield (Inner P v) U → InitYield (Q v) U)
    (R : System A n) (hR : DirectResolution (flatten P) R) :
    ∃ U : System A n, DirectResolution (flatten (withLabels P Q)) U ∧
      UnfoldsTo R.val U.val := by
  classical
  obtain ⟨T, V, ⟨r⟩, hV, f, hf⟩ :=
    ResolutionFactorization.resolution_to_flatten_resolution P R hR
  have chosen (v : T.val.Vertex) := ResolutionLifting.transfer_initial
    (hQ (r.vertex v)) (T.val.graph.label v).2 (r.variableMap v) (r.resolves v)
  let q := fun v => Classical.choose (chosen v)
  have hr (v) := (Classical.choose_spec (chosen v)).1
  have hu (v) := (Classical.choose_spec (chosen v)).2
  let T' : System (System A) n := ⟨withLabels T.val q, T.property⟩
  let r' : FlattenResolution (withLabels P Q) T' := {
    vertex := r.vertex
    variableMap := r.variableMap
    initial := r.initial
    resolves := hr
    transition := r.transition
    exit := r.exit }
  obtain ⟨V', hV'⟩ := Flattening.flatten_system T'
  have hh : UnfoldEquivalent V.val V'.val := by
    apply SystemSubstitution.pointwise_unfold T (fun v => (T.val.graph.label v).2) q
      (fun v => ⟨(q v).val, hu v,
        ⟨MorphismTheorems.identity _, MorphismTheorems.identity_surjective _⟩⟩) V V'
    · exact hV
    · exact hV'
  obtain ⟨W, ⟨a⟩, ⟨b⟩⟩ := SystemSubstitution.common_system V V' hh
  obtain ⟨g⟩ := Flattening.flatten_resolution_sound _ T' r' V' hV'
  exact ⟨W, ⟨MorphismTheorems.compose b g⟩,
    ⟨MorphismTheorems.compose a f,
      MorphismTheorems.system_morphism_locally_surjective W R _⟩⟩

/--
---
conclusion: Lax369799.YieldSubstitution.transfer_resolution
---
Factor the resolution into a flatten-resolution. Transfer its local
resolutions without changing their variable maps, and flatten again.
A common unfolding gives a direct resolution above the original system.
-/
theorem transfer_resolution {A : RankedSet} {n : ℕ}
    (P : SetSystem (SetSystem A) n) (Q : ∀ v, SetSystem A (P.graph.label v).1)
    (hQ : ∀ v, YieldBelow (Inner P v) (Q v))
    (R : System A n) (hR : DirectResolution (flatten P) R) :
    ∃ U : System A n, DirectResolution (flatten (withLabels P Q)) U ∧
      UnfoldsTo R.val U.val :=
  transfer_initial_resolution P Q (fun v => ResolutionLifting.initial_mono (hQ v)) R hR

end Lax369799Proofs.YieldSubstitution
