import Lax369799Proofs.MuCalculus
import Mathlib.Order.FixedPoints
import Mathlib.Data.Set.Lattice

namespace Lax369799Proofs.MuBisimulation
open Lax369799
open TransitionSystems ModalMuCalculus

private def Coherent {V W : Type} (R : V → W → Prop) (X : Set V) (Y : Set W) : Prop :=
  ∀ v w, R v w → (v ∈ X ↔ w ∈ Y)

private def pairMap {V W : Type} (F : Set V →o Set V) (G : Set W →o Set W) :
    Set V × Set W →o Set V × Set W where
  toFun := fun p => (F p.1, G p.2)
  monotone' := fun _ _ h => ⟨F.monotone h.1, G.monotone h.2⟩

private theorem pair_lfp {V W : Type} (F : Set V →o Set V) (G : Set W →o Set W) :
    (pairMap F G).lfp = (F.lfp, G.lfp) := by
  apply le_antisymm
  · apply OrderHom.lfp_le
    exact ⟨F.map_lfp.le, G.map_lfp.le⟩
  · have h := (pairMap F G).map_lfp
    exact ⟨F.lfp_le (congrArg Prod.fst h).le, G.lfp_le (congrArg Prod.snd h).le⟩

private theorem pair_gfp {V W : Type} (F : Set V →o Set V) (G : Set W →o Set W) :
    (pairMap F G).gfp = (F.gfp, G.gfp) := by
  apply le_antisymm
  · have h := (pairMap F G).map_gfp
    exact ⟨F.le_gfp (congrArg Prod.fst h).ge, G.le_gfp (congrArg Prod.snd h).ge⟩
  · apply OrderHom.le_gfp
    exact ⟨F.map_gfp.ge, G.map_gfp.ge⟩

private theorem coherent_lfp {V W : Type} (R : V → W → Prop)
    (F : Set V →o Set V) (G : Set W →o Set W)
    (h : ∀ X Y, Coherent R X Y → Coherent R (F X) (G Y)) : Coherent R F.lfp G.lfp := by
  have hc : Coherent R (pairMap F G).lfp.1 (pairMap F G).lfp.2 := by
    apply (pairMap F G).lfp_induction (p := fun p => Coherent R p.1 p.2)
    · intro p hp _
      exact h p.1 p.2 hp
    · intro s hs v w hvw
      change (∃ X ∈ Prod.fst '' s, v ∈ X) ↔ (∃ Y ∈ Prod.snd '' s, w ∈ Y)
      constructor
      · rintro ⟨X, ⟨p, hp, rfl⟩, hv⟩
        exact ⟨p.2, ⟨p, hp, rfl⟩, (hs p hp v w hvw).mp hv⟩
      · rintro ⟨Y, ⟨p, hp, rfl⟩, hw⟩
        exact ⟨p.1, ⟨p, hp, rfl⟩, (hs p hp v w hvw).mpr hw⟩
  simpa only [pair_lfp] using hc

private theorem coherent_gfp {V W : Type} (R : V → W → Prop)
    (F : Set V →o Set V) (G : Set W →o Set W)
    (h : ∀ X Y, Coherent R X Y → Coherent R (F X) (G Y)) : Coherent R F.gfp G.gfp := by
  have hc : Coherent R (pairMap F G).gfp.1 (pairMap F G).gfp.2 := by
    apply (pairMap F G).gfp_induction (p := fun p => Coherent R p.1 p.2)
    · intro p hp _
      exact h p.1 p.2 hp
    · intro s hs v w hvw
      change (∀ X ∈ Prod.fst '' s, v ∈ X) ↔ (∀ Y ∈ Prod.snd '' s, w ∈ Y)
      constructor
      · intro hv Y hY
        obtain ⟨p, hp, rfl⟩ := hY
        exact (hs p hp v w hvw).mp (hv p.1 ⟨p, hp, rfl⟩)
      · intro hw X hX
        obtain ⟨p, hp, rfl⟩ := hX
        exact (hs p hp v w hvw).mpr (hw p.2 ⟨p, hp, rfl⟩)
  simpa only [pair_gfp] using hc

private def bodyMap {P : Type} (S : TransitionSystem P) {n : ℕ}
    (φ : Formula P (n + 1)) (ρ : Fin n → Set S.Vertex) : Set S.Vertex →o Set S.Vertex where
  toFun := fun X => φ.eval S (Fin.cases X ρ)
  monotone' := by
    intro X Y h
    apply Lax369799Proofs.MuCalculus.eval_monotone
    intro i
    exact Fin.cases h (fun _ => Set.Subset.rfl) i

private theorem eval_coherent {P : Type} (S T : TransitionSystem P)
    (R : S.Vertex → T.Vertex → Prop) (hR : Bisimulation S T R)
    {n : ℕ} (φ : Formula P n) (ρ : Fin n → Set S.Vertex) (σ : Fin n → Set T.Vertex)
    (henv : ∀ i, Coherent R (ρ i) (σ i)) : Coherent R (φ.eval S ρ) (φ.eval T σ) := by
  induction φ with
  | top => intro v w _; exact Iff.rfl
  | bot => intro v w _; exact Iff.rfl
  | proposition p =>
    intro v w hvw
    change p ∈ S.valuation v ↔ p ∈ T.valuation w
    rw [(hR.2 v w hvw).1]
  | negProposition p =>
    intro v w hvw
    change p ∉ S.valuation v ↔ p ∉ T.valuation w
    rw [(hR.2 v w hvw).1]
  | «variable» i => exact henv i
  | conj φ ψ ihφ ihψ =>
    intro v w hvw
    exact and_congr (ihφ ρ σ henv v w hvw) (ihψ ρ σ henv v w hvw)
  | disj φ ψ ihφ ihψ =>
    intro v w hvw
    exact or_congr (ihφ ρ σ henv v w hvw) (ihψ ρ σ henv v w hvw)
  | diamond φ ih =>
    intro v w hvw
    constructor
    · rintro ⟨v', hv', hφ⟩
      obtain ⟨w', hw', hr⟩ := (hR.2 v w hvw).2.1 v' hv'
      exact ⟨w', hw', (ih ρ σ henv v' w' hr).mp hφ⟩
    · rintro ⟨w', hw', hφ⟩
      obtain ⟨v', hv', hr⟩ := (hR.2 v w hvw).2.2 w' hw'
      exact ⟨v', hv', (ih ρ σ henv v' w' hr).mpr hφ⟩
  | box φ ih =>
    intro v w hvw
    constructor
    · intro h w' hw'
      obtain ⟨v', hv', hr⟩ := (hR.2 v w hvw).2.2 w' hw'
      exact (ih ρ σ henv v' w' hr).mp (h v' hv')
    · intro h v' hv'
      obtain ⟨w', hw', hr⟩ := (hR.2 v w hvw).2.1 v' hv'
      exact (ih ρ σ henv v' w' hr).mpr (h w' hw')
  | mu φ ih =>
    apply coherent_lfp R (bodyMap S φ ρ) (bodyMap T φ σ)
    intro X Y hXY
    exact ih (Fin.cases X ρ) (Fin.cases Y σ) (fun i => Fin.cases hXY henv i)
  | nu φ ih =>
    apply coherent_gfp R (bodyMap S φ ρ) (bodyMap T φ σ)
    intro X Y hXY
    exact ih (Fin.cases X ρ) (Fin.cases Y σ) (fun i => Fin.cases hXY henv i)

/--
---
conclusion: Lax369799.MuCalculusTheorems.mu_bisimulation_invariant
---
Induct on formulas using coherent environments along a bisimulation.
Coherent pairs of sets are closed under arbitrary coordinatewise unions
and intersections. Fixed-point induction on the product lattice therefore
preserves coherence for both least and greatest fixed points.
-/
theorem mu_bisimulation_invariant {P : Type} (φ : Sentence P) :
    BisimulationInvariant {S | Models S φ} := by
  intro S T h
  obtain ⟨R, hR⟩ := h
  exact eval_coherent S T R hR φ Fin.elim0 Fin.elim0 (fun i => Fin.elim0 i)
    S.initial T.initial hR.1

end Lax369799Proofs.MuBisimulation
