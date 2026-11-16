import Lax369799.ContextResolutionApproximation
import Lax369799Proofs.FiniteResolutionApproximation
import Lax369799Proofs.ContextCongruence
import Lax369799Proofs.Yields
import Lax369799Proofs.RootResolutionApproximation

set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
namespace Lax369799Proofs.ContextResolutionApproximation
open Lax369799.RankedSystems Lax369799.Morphisms Lax369799.Flattening
open Lax369799.FiniteResolutionNormalForms
open Lax369799Proofs.Pullbacks

private theorem hole_family {A : RankedSet} {k r m : ℕ} (S : SetSystem A k)
    (a : WithHole A k r) (ha : IsHole ⟨r, a⟩)
    (c : Fin m → Component (substitution S r a)) (hc : ∀ i, (c i).rooted = false) :
    ∃ d : Fin m → Component S, (∀ i, (d i).rooted = false) ∧
      ∀ i, DirectResolution (substitution (trim (family d).graph) r a) (c i).system := by
  cases a with
  | inl a => obtain ⟨h, he⟩ := ha; cases he
  | inr h =>
    obtain ⟨h⟩ := h
    subst r
    refine ⟨c, hc, ?_⟩
    intro i
    change DirectResolution (trim (family c).graph) (c i).system
    have hi := FiniteResolutionNormalForms.injectionResolution c i
    simpa only [hc, Bool.false_eq_true, ↓reduceIte] using hi

theorem substitution_nonhole {A : RankedSet} {k r : ℕ}
    (S Q : SetSystem A k) (a : WithHole A k r) (ha : ¬ IsHole ⟨r, a⟩) :
    substitution Q r a = substitution S r a := by
  cases a with
  | inl a => rfl
  | inr h => exact False.elim (ha ⟨h, rfl⟩)

/--
---
conclusion: Lax369799.ContextResolutionApproximation.direct_approximation
---
Select the finite support at the unique hole. Every other label retains
its original resolutions; each selected hole resolution maps into the
finite disjoint family.
-/
theorem direct_approximation {A : RankedSet} {k n : ℕ}
    (C : SetContext A k n) (S : SetSystem A k) (R : System A n)
    (hR : DirectResolution (plug C S) R) :
    ∃ (m : ℕ) (c : Fin m → Component S) (U : System A n),
      (∀ i, (c i).rooted = false) ∧
      DirectResolution (plug C (trim (family c).graph)) U ∧ UnfoldsTo R.val U.val := by
  classical
  let P := relabel (substitution S) C.system
  obtain ⟨m, c, hc, hs⟩ := FiniteResolutionApproximation.finite_support P R hR
  obtain ⟨v₀, hv₀, unique⟩ := C.one_hole
  obtain ⟨d, hd, hdi⟩ := hole_family S (C.system.graph.label v₀).2 hv₀ (c v₀) (hc v₀)
  let Q := trim (family d).graph
  obtain ⟨U, hu, hr⟩ := hs (fun v => substitution Q _ (C.system.graph.label v).2) (by
    intro v i
    by_cases hv : IsHole (C.system.graph.label v)
    · have he := unique v hv
      subst v
      exact hdi i
    · change DirectResolution (substitution Q _ (C.system.graph.label v).2) (c v i).system
      rw [substitution_nonhole S Q _ hv]
      have hi := (c v i).resolves
      simp only [hc, Bool.false_eq_true, ↓reduceIte] at hi
      exact hi)
  exact ⟨m v₀, d, U, hd, hu, hr⟩

/--
---
conclusion: Lax369799.ContextResolutionApproximation.initial_yields
---
Apply finite approximation to a direct-resolution witness and compose
its unfolding. Conversely the disjoint family maps into the original
system, and this morphism extends through the context.
-/
theorem initial_yields {A : RankedSet} {k n : ℕ}
    (C : SetContext A k n) (S : SetSystem A k) (R : System A n) :
    InitYield (plug C S) R ↔
      ∃ (m : ℕ) (c : Fin m → Component S),
        (∀ i, (c i).rooted = false) ∧ InitYield (plug C (trim (family c).graph)) R := by
  constructor
  · rintro ⟨D, hd, ⟨f, hf⟩⟩
    obtain ⟨m, c, U, hc, hu, g, hg⟩ := direct_approximation C S D hd
    exact ⟨m, c, hc, U, hu, MorphismTheorems.compose g f,
      MorphismTheorems.system_morphism_locally_surjective U R _⟩
  · rintro ⟨m, c, _, hr⟩
    let f := project (FiniteResolutionNormalForms.familyMap c)
    have h : ∀ r a, Morphism (substitution (trim (family c).graph) r a) (substitution S r a) := by
      intro r a
      cases a with
      | inl a => exact MorphismTheorems.identity _
      | inr h => obtain ⟨h⟩ := h; subst r; exact f
    exact Yields.initial_yield_forward
      (ContextCongruence.flatten_label_morphism C.system _ _ h) hr

theorem hole_component {A : RankedSet} {k r : ℕ} (S : SetSystem A k)
    (a : WithHole A k r) (ha : IsHole ⟨r, a⟩) (c : Component (substitution S r a)) :
    ∃ d : Component S, ∀ Q : SetSystem A k,
      DirectResolution (if c.rooted then uproot (substitution Q r a) else substitution Q r a) c.system ↔
      DirectResolution (if d.rooted then uproot Q else Q) d.system := by
  cases a with
  | inl a => obtain ⟨h, he⟩ := ha; cases he
  | inr h => obtain ⟨h⟩ := h; subst r; exact ⟨c, fun _ => Iff.rfl⟩

private theorem family_below {A : RankedSet} {k n m : ℕ}
    (C : SetContext A k n) (S : SetSystem A k) (c : Fin m → Component S) :
    YieldBelow (plug C (trim (family c).graph)) (plug C S) := by
  let f := project (FiniteResolutionNormalForms.familyMap c)
  exact YieldObservations.yield_context_congruence C _ _ (Yields.morphism_yields f).1

private theorem root_plug_observation {A : RankedSet} {k n : ℕ}
    (C : SetContext A k n) (S : SetSystem A k) (R : System A n) :
    InitYield (uproot (plug C S)) R ↔
      InitYield (trim (Lax369799.RootExpansion.startAtRoots
        (Lax369799.FinitePresentations.flattenPresentation
          (Lax369799.ObservedSubstitution.finiteLabels (relabel (substitution S) C.system).graph)))) R := by
  exact YieldObservations.obs_cover
    (PresentationObservations.rootedCover (FiniteAcceptance.trimProjection _)) R

/--
---
conclusion: Lax369799.ContextResolutionApproximation.root_yields
---
Take finite support in the root-entry expansion. Select all support
components located at the hole, retaining their initial or root entry
flags, and insert their disjoint family. The reverse inclusion follows
from the family's morphism to the original hole label.
-/
theorem root_yields {A : RankedSet} {k n : ℕ}
    (C : SetContext A k n) (S : SetSystem A k) (R : System A n) :
    InitYield (uproot (plug C S)) R ↔
      ∃ (m : ℕ) (c : Fin m → Component S),
        InitYield (uproot (plug C (trim (family c).graph))) R := by
  classical
  constructor
  · intro hr
    let P := (relabel (substitution S) C.system).graph
    have hr := (root_plug_observation C S R).mp hr
    obtain ⟨m, v, c, hs⟩ := RootResolutionApproximation.finite_support P R hr
    let I := {i : Fin m // IsHole (C.system.graph.label (v i))}
    let e := Fintype.equivFin I
    have hchoice (i : I) := hole_component S (C.system.graph.label (v i.val)).2 i.property (c i.val)
    let d := fun i : I => Classical.choose (hchoice i)
    have hd (i : I) := Classical.choose_spec (hchoice i)
    let ds := fun j => d (e.symm j)
    let Q := trim (family ds).graph
    have hsupport : ∀ i, DirectResolution
        (if (c i).rooted then uproot (substitution Q _ (C.system.graph.label (v i)).2)
         else substitution Q _ (C.system.graph.label (v i)).2) (c i).system := by
      intro i
      by_cases hi : IsHole (C.system.graph.label (v i))
      · apply (hd ⟨i, hi⟩ Q).mpr
        have hh := FiniteResolutionNormalForms.injectionResolution ds (e ⟨i, hi⟩)
        change DirectResolution (if (d (e.symm (e ⟨i, hi⟩))).rooted then uproot Q else Q)
          (d (e.symm (e ⟨i, hi⟩))).system at hh
        rw [e.symm_apply_apply] at hh
        exact hh
      · rw [substitution_nonhole S Q _ hi]
        exact (c i).resolves
    have hr := hs (fun w => substitution Q _ (C.system.graph.label w).2) hsupport
    refine ⟨Fintype.card I, ds, ?_⟩
    change InitYield (uproot (plug C Q)) R
    apply (root_plug_observation C Q R).mpr
    exact hr
  · rintro ⟨m, c, hr⟩
    have hy := family_below C S c (plant R.val) (Or.inr ⟨R, hr, rfl⟩)
    rcases hy with ⟨U, _, he⟩ | ⟨U, hu, he⟩
    · exact False.elim (PlantAcceptance.system_ne_plant U R he.symm)
    · exact (PlantAcceptance.plant_injective R U he).symm ▸ hu

/--
---
conclusion: Lax369799.ContextResolutionApproximation.yields
---
Combine initial and root approximation, keeping each deterministic
component's entry flag. The family maps into the original system.
-/
theorem yields {A : RankedSet} {k n : ℕ}
    (C : SetContext A k n) (S : SetSystem A k) (R : SetSystem A n) :
    Yield (plug C S) R ↔
      ∃ (m : ℕ) (c : Fin m → Component S),
        Yield (plug C (trim (family c).graph)) R := by
  constructor
  · rintro (⟨U, hu, rfl⟩ | ⟨U, hu, rfl⟩)
    · obtain ⟨m, c, _, hc⟩ := (initial_yields C S U).mp hu
      exact ⟨m, c, Or.inl ⟨U, hc, rfl⟩⟩
    · obtain ⟨m, c, hc⟩ := (root_yields C S U).mp hu
      exact ⟨m, c, Or.inr ⟨U, hc, rfl⟩⟩
  · rintro ⟨m, c, hc⟩
    exact family_below C S c R hc

end Lax369799Proofs.ContextResolutionApproximation
