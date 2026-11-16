import Lax369799.UnrestrictedLogic
import Mathlib.Order.FixedPoints
import Mathlib.Data.Set.Lattice

namespace Lax369799Proofs.UnrestrictedLogic
set_option backward.isDefEq.respectTransparency false
open Lax369799 UnrestrictedTransitionSystems Lax369799.UnrestrictedLogic

/--
---
conclusion: Lax369799.UnrestrictedLogic.finite_mu
---
-/
theorem finite_mu {P : Type} (S : TransitionSystems.TransitionSystem P) {n : ℕ}
    (φ : ModalMuCalculus.Formula P n) (ρ : Fin n → Set S.Vertex) :
    muEval (ofFinite S) φ ρ = φ.eval S ρ := by
  induction φ with
  | top | bot | proposition | negProposition | «variable» => rfl
  | conj φ ψ ihφ ihψ => exact congrArg₂ Set.inter (ihφ ρ) (ihψ ρ)
  | disj φ ψ ihφ ihψ => exact congrArg₂ Set.union (ihφ ρ) (ihψ ρ)
  | diamond φ ih => exact congrArg (fun X => {v | ∃ w, S.edge v w ∧ w ∈ X}) (ih ρ)
  | box φ ih => exact congrArg (fun X => {v | ∀ w, S.edge v w → w ∈ X}) (ih ρ)
  | mu φ ih =>
    apply congrArg sInf
    ext X
    change muEval (ofFinite S) φ (Fin.cases X ρ) ⊆ X ↔ φ.eval S (Fin.cases X ρ) ⊆ X
    rw [ih]
  | nu φ ih =>
    apply congrArg sSup
    ext X
    change X ⊆ muEval (ofFinite S) φ (Fin.cases X ρ) ↔ X ⊆ φ.eval S (Fin.cases X ρ)
    rw [ih]

/--
---
conclusion: Lax369799.UnrestrictedLogic.finite_mso
---
-/
theorem finite_mso {P : Type} (S : TransitionSystems.TransitionSystem P) {m n : ℕ}
    (φ : MonadicSecondOrder.Formula P m n) (ρ : Fin m → S.Vertex) (σ : Fin n → Set S.Vertex) :
    msoEval (ofFinite S) φ ρ σ ↔ φ.eval S ρ σ := by
  induction φ with
  | equal | initial | proposition | edge | member => rfl
  | neg φ ih => exact not_congr (ih ρ σ)
  | disj φ ψ ihφ ihψ => exact or_congr (ihφ ρ σ) (ihψ ρ σ)
  | existsVertex φ ih => exact exists_congr (fun v => ih (Fin.cases v ρ) σ)
  | existsSet φ ih => exact exists_congr (fun X => ih ρ (Fin.cases X σ))

/--
---
conclusion: Lax369799.UnrestrictedLogic.eval_monotone
---
-/
theorem eval_monotone {P : Type} (S : TransitionSystem P) {n : ℕ}
    (φ : ModalMuCalculus.Formula P n) (ρ σ : Fin n → Set S.Vertex)
    (h : ∀ i, ρ i ⊆ σ i) : muEval S φ ρ ⊆ muEval S φ σ := by
  induction φ with
  | top => exact Set.Subset.rfl
  | bot => exact Set.Subset.rfl
  | proposition p => exact Set.Subset.rfl
  | negProposition p => exact Set.Subset.rfl
  | «variable» i => exact h i
  | conj φ ψ ihφ ihψ => exact Set.inter_subset_inter (ihφ ρ σ h) (ihψ ρ σ h)
  | disj φ ψ ihφ ihψ => exact Set.union_subset_union (ihφ ρ σ h) (ihψ ρ σ h)
  | diamond φ ih =>
    rintro v ⟨w, he, hw⟩
    exact ⟨w, he, ih ρ σ h hw⟩
  | box φ ih =>
    intro v hv w he
    exact ih ρ σ h (hv w he)
  | mu φ ih =>
    apply le_sInf
    intro X hX
    apply sInf_le
    exact (ih (Fin.cases X ρ) (Fin.cases X σ) (by intro i; refine Fin.cases ?_ ?_ i; exact Set.Subset.rfl; exact h)).trans hX
  | nu φ ih =>
    apply sSup_le
    intro X hX
    apply le_sSup
    exact hX.trans (ih (Fin.cases X ρ) (Fin.cases X σ) (by intro i; refine Fin.cases ?_ ?_ i; exact Set.Subset.rfl; exact h))


/--
---
conclusion: Lax369799.UnrestrictedLogic.translate_correct
---
-/
theorem translate_correct {P : Type} (S : TransitionSystem P) {n : ℕ}
    (φ : ModalMuCalculus.Formula P n) {m : ℕ} (x : Fin m)
    (ρ : Fin m → S.Vertex) (σ : Fin n → Set S.Vertex) :
    msoEval S (translate φ x) ρ σ ↔ ρ x ∈ muEval S φ σ := by
  classical
  induction φ generalizing m with
  | top => simp [translate, msoEval, muEval]
  | bot => simp [translate, msoEval, muEval]
  | proposition p => rfl
  | negProposition p => rfl
  | «variable» i => rfl
  | conj φ ψ ihφ ihψ =>
    simp [translate, conjunction, msoEval,
      muEval, ihφ, ihψ]
  | disj φ ψ ihφ ihψ =>
    simp [translate, msoEval, muEval, ihφ, ihψ]
  | diamond φ ih =>
    simp [translate, conjunction, msoEval,
      muEval, ih]
  | box φ ih =>
    simp [translate, allVertex, implication, msoEval,
      muEval, ih]
  | mu φ ih =>
    simp [translate, allSet, allVertex, implication, msoEval,
      muEval, ih, Set.subset_def]
  | nu φ ih =>
    simp [translate, conjunction, allVertex, implication, msoEval,
      muEval, ih, Set.subset_def, and_comm]


/--
---
conclusion: Lax369799.UnrestrictedLogic.mu_to_mso
---
-/
theorem mu_to_mso {P : Type} (φ : ModalMuCalculus.Sentence P) :
    ∃ ψ : MonadicSecondOrder.Sentence P, ∀ S : TransitionSystem P,
      MuModels S φ ↔ MSOModels S ψ := by
  classical
  refine ⟨sentence φ,?_⟩
  intro S
  simp [sentence,conjunction,MSOModels,msoEval,translate_correct,MuModels]

open ModalMuCalculus (Formula Sentence)

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
  toFun := fun X => muEval S φ (Fin.cases X ρ)
  monotone' := by
    intro X Y h
    apply eval_monotone
    intro i
    exact Fin.cases h (fun _ => Set.Subset.rfl) i

private theorem eval_coherent {P : Type} (S T : TransitionSystem P)
    (R : S.Vertex → T.Vertex → Prop) (hR : Bisimulation S T R)
    {n : ℕ} (φ : Formula P n) (ρ : Fin n → Set S.Vertex) (σ : Fin n → Set T.Vertex)
    (henv : ∀ i, Coherent R (ρ i) (σ i)) : Coherent R (muEval S φ ρ) (muEval T φ σ) := by
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
conclusion: Lax369799.UnrestrictedLogic.mu_bisimulation_invariant
---
-/
theorem mu_bisimulation_invariant {P : Type} (φ : ModalMuCalculus.Sentence P) :
    BisimulationInvariant {S | MuModels S φ} := by
  intro S T h
  obtain ⟨R,hR⟩ := h
  exact eval_coherent S T R hR φ Fin.elim0 Fin.elim0 (fun i => Fin.elim0 i)
    S.initial T.initial hR.1

/--
---
conclusion: Lax369799.UnrestrictedLogic.mu_definable_implies_mso_invariant
---
-/
theorem mu_definable_implies_mso_invariant {P : Type} (L : Set (TransitionSystem P))
    (hL : MuDefinable L) : MSODefinable L ∧ BisimulationInvariant L := by
  obtain ⟨φ,hφ⟩ := hL
  obtain ⟨ψ,hψ⟩ := mu_to_mso φ
  refine ⟨⟨ψ,fun S => (hφ S).trans (hψ S)⟩,?_⟩
  intro S T hST
  exact (hφ S).trans ((mu_bisimulation_invariant φ S T hST).trans (hφ T).symm)

/--
---
conclusion: Lax369799.UnrestrictedLogic.finite_bisimulation
---
-/
theorem finite_bisimulation {P : Type} (S T : TransitionSystems.TransitionSystem P)
    (R : S.Vertex → T.Vertex → Prop) :
    Bisimulation (ofFinite S) (ofFinite T) R ↔ TransitionSystems.Bisimulation S T R := Iff.rfl

/--
---
conclusion: Lax369799.UnrestrictedLogic.finite_mu_models
---
-/
theorem finite_mu_models {P : Type} (S : TransitionSystems.TransitionSystem P)
    (φ : ModalMuCalculus.Sentence P) : MuModels (ofFinite S) φ ↔ ModalMuCalculus.Models S φ :=
  Iff.of_eq (congrArg (fun X : Set S.Vertex => S.initial ∈ X) (finite_mu S φ Fin.elim0))

/--
---
conclusion: Lax369799.UnrestrictedLogic.finite_mso_models
---
-/
theorem finite_mso_models {P : Type} (S : TransitionSystems.TransitionSystem P)
    (φ : MonadicSecondOrder.Sentence P) : MSOModels (ofFinite S) φ ↔ MonadicSecondOrder.Models S φ :=
  finite_mso S φ Fin.elim0 Fin.elim0

end Lax369799Proofs.UnrestrictedLogic
