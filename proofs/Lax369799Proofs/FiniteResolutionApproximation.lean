import Lax369799.FiniteResolutionApproximation
import Lax369799Proofs.FiniteResolutionNormalForms
import Lax369799Proofs.ResolutionFactorization

set_option backward.isDefEq.respectTransparency false
namespace Lax369799Proofs.FiniteResolutionApproximation
open Lax369799.RankedSystems Lax369799.Morphisms Lax369799.Flattening Lax369799.Resolutions
open Lax369799.Renaming Lax369799.FiniteResolutionNormalForms Lax369799.FiniteResolutionApproximation

private def component {A : RankedSet} {n : ℕ} {S : SetSystem (SetSystem A) n}
    {T : System (System A) n} (h : FlattenResolution S T) (v : S.Vertex)
    (t : {t : T.val.Vertex // h.vertex t = v}) : Component (Inner S v) := by
  obtain ⟨t, ht⟩ := t
  subst v
  exact ⟨renameSystem (h.variableMap t) (T.val.graph.label t).2, false, h.resolves t⟩

private theorem component_root {A : RankedSet} {n : ℕ} {S : SetSystem (SetSystem A) n}
    {T : System (System A) n} (h : FlattenResolution S T) (v : S.Vertex)
    (t : {t : T.val.Vertex // h.vertex t = v}) : (component h v t).rooted = false := by
  obtain ⟨t, ht⟩ := t
  subst v
  rfl

/--
---
conclusion: Lax369799.FiniteResolutionApproximation.finite_support
---
Collect the renamed inner systems in the fibres of a flatten-resolution.
Any replacement admitting these systems admits the same flatten-resolution.
-/
theorem finite_support {A : RankedSet} {n : ℕ}
    (S : SetSystem (SetSystem A) n) (R : System A n)
    (hR : DirectResolution (flatten S) R) :
    ∃ (k : S.Vertex → ℕ) (c : ∀ v, Fin (k v) → Component (Inner S v)),
      (∀ v i, (c v i).rooted = false) ∧
      ∀ (Q : ∀ v, SetSystem A (S.graph.label v).1),
        (∀ v i, DirectResolution (Q v) (c v i).system) →
        ∃ U : System A n,
          DirectResolution (flatten (Lax369799.ProfileSubstitution.withLabels S Q)) U ∧
          UnfoldsTo R.val U.val := by
  classical
  obtain ⟨T, U, ⟨h⟩, hu, hru⟩ := ResolutionFactorization.resolution_to_flatten_resolution S R hR
  let I := fun v => {t : T.val.Vertex // h.vertex t = v}
  let k := fun v => Fintype.card (I v)
  let e := fun v => Fintype.equivFin (I v)
  let c := fun v (i : Fin (k v)) => component h v ((e v).symm i)
  refine ⟨k, c, fun v i => component_root h v ((e v).symm i), ?_⟩
  intro Q hQ
  have hh : FlattenResolution (Lax369799.ProfileSubstitution.withLabels S Q) T := {
    vertex := h.vertex
    variableMap := h.variableMap
    initial := h.initial
    transition := h.transition
    exit := h.exit
    resolves := by
      intro t
      have hi := hQ (h.vertex t) (e (h.vertex t) ⟨t, rfl⟩)
      change DirectResolution (Q (h.vertex t))
        (renameSystem (h.variableMap t) (T.val.graph.label t).2)
      simpa only [c, Equiv.symm_apply_apply, component] using hi }
  exact ⟨U, Flattening.flatten_resolution_sound _ T hh U hu, hru⟩

/--
---
conclusion: Lax369799.FiniteResolutionApproximation.direct_approximation
---
Each selected component maps into its disjoint family, so the finite
support property applies to the families themselves.
-/
theorem direct_approximation {A : RankedSet} {n : ℕ}
    (S : SetSystem (SetSystem A) n) (R : System A n)
    (hR : DirectResolution (flatten S) R) :
    ∃ (k : S.Vertex → ℕ) (c : ∀ v, Fin (k v) → Component (Inner S v)) (U : System A n),
      (∀ v i, (c v i).rooted = false) ∧
      DirectResolution (flatten (replace S k c)) U ∧ UnfoldsTo R.val U.val := by
  obtain ⟨k, c, hc, hs⟩ := finite_support S R hR
  obtain ⟨U, hu, hr⟩ := hs (fun v => trim (family (c v)).graph) (by
    intro v i
    have hi := FiniteResolutionNormalForms.injectionResolution (c v) i
    simpa only [hc, Bool.false_eq_true, ↓reduceIte] using hi)
  exact ⟨k, c, U, hc, hu, hr⟩

end Lax369799Proofs.FiniteResolutionApproximation
