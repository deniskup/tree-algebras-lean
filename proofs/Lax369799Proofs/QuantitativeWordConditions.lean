import Lax369799.QuantitativeWordConditions
import Lax369799Proofs.QuantitativeDeterminization
import Lax369799Proofs.AlgebraicBranchCondition
import Mathlib.Tactic.Ring

set_option backward.isDefEq.respectTransparency false
namespace Lax369799Proofs.QuantitativeWordConditions
open Lax369799
open UnfoldAutomata OmegaDeterminization WordFactorization
open Lax369799.QuantitativeWordConditions

private theorem state_card (M : Type) [Finite M] :
    Nat.card (OmegaProducts.State M) ≤ 4*(Nat.card M)^3 := by
  have h := Nat.card_le_card_of_injective
    (fun s : OmegaProducts.State M => (s.a,s.e,s.inPrefix,s.value,s.cut)) (by
      intro a b h
      cases a;cases b
      simp only [Prod.mk.injEq] at h
      obtain ⟨rfl,rfl,rfl,rfl,rfl⟩ := h
      rfl)
  apply h.trans_eq
  have hb : Nat.card Bool = 2 := by simp [Nat.card_eq_fintype_card]
  simp only [Nat.card_prod,hb]
  ring

private theorem product_regular {M : Type} [Monoid M] [Finite M] {u z : ℕ}
    (f : Fin u → M) (P : M → M → Prop) (cap : ℕ) (hc : Nat.card M ≤ cap) :
    ∃ D : WordCondition u z,
      (∀ w,D.AcceptsInfinite w ↔ OmegaProducts.Accepts f P w) ∧
      D.states ≤ QuantitativeDeterminization.stateBound (4*cap^3) ∧
      (∀ q,D.priority q ≤ QuantitativeDeterminization.priorityBound (4*cap^3)) := by
  classical
  let : Fintype (OmegaProducts.State M) := Fintype.ofFinite _
  let e := Fintype.equivFin (OmegaProducts.State M)
  let B : Buchi u := {
    states := Fintype.card (OmegaProducts.State M)
    initial := {q | OmegaProducts.Initial P (e.symm q)}
    transition := fun q b t => OmegaProducts.Step (e.symm q) (f b) (e.symm t)
    accepting := {q | (e.symm q).cut = true} }
  have hb : B.states ≤ 4*cap^3 := by
    change Fintype.card (OmegaProducts.State M) ≤ _
    rw [← Nat.card_eq_fintype_card]
    exact (state_card M).trans (Nat.mul_le_mul_left 4 (Nat.pow_le_pow_left hc 3))
  obtain ⟨D,hD,hs,hp⟩ := QuantitativeDeterminization.determinization_bound (z := z) B (4*cap^3) hb
  refine ⟨D,?_,hs,hp⟩
  intro w
  apply (hD w).trans
  constructor
  · rintro ⟨r,hi,ht,ha⟩
    exact OmegaProducts.sound (r := fun n => e.symm (r n)) hi ht ha
  · intro h
    obtain ⟨r,hi,ht,ha⟩ := OmegaProducts.complete h
    refine ⟨fun n => e (r n),?_,?_,?_⟩
    · simpa only [B,Set.mem_ofPred_eq,e.symm_apply_apply] using hi
    · simpa only [B,e.symm_apply_apply] using ht
    · simpa only [B,Set.mem_ofPred_eq,e.symm_apply_apply] using ha

private theorem omega_regular {A : RankedSystems.RankedSet} (E : FiniteSyntacticAlgebra.Algebra A)
    (F : Set (A 0)) [Fintype (A 1)] {z : ℕ} (u : ℕ) (hu : Fintype.card (A 1) ≤ u) :
    ∃ D : WordCondition (Fintype.card (A 1)) z,
      (∀ w,D.AcceptsInfinite w ↔ AlgebraicOmegaWords.Accepts E F
        (fun n => (Fintype.equivFin (A 1)).symm (w n))) ∧
      D.states ≤ QuantitativeDeterminization.stateBound (buchiBound u) ∧
      (∀ q,D.priority q ≤ priorityBound u) := by
  classical
  let : Semigroup (A 1) := { mul := UnaryComposition.product E,mul_assoc := UnaryComposition.associative E }
  let : Finite (WithOne (A 1)) := inferInstanceAs (Finite (Option (A 1)))
  let f : Fin (Fintype.card (A 1)) → WithOne (A 1) := fun i =>
    ((Fintype.equivFin (A 1)).symm i : WithOne (A 1))
  let P : WithOne (A 1) → WithOne (A 1) → Prop := fun x y =>
    ∃ a e : A 1,(a : WithOne (A 1)) = x ∧ (e : WithOne (A 1)) = y ∧ E.eval 0 (UnaryFactorization.lasso a e) ∈ F
  have hc : Nat.card (WithOne (A 1)) ≤ u+1 := by
    change Nat.card (Option (A 1)) ≤ u+1
    simpa only [Nat.card_eq_fintype_card,Fintype.card_option] using Nat.add_le_add_right hu 1
  obtain ⟨D,hD,hs,hp⟩ := product_regular (z := z) f P (u+1) hc
  refine ⟨D,fun w => (hD w).trans ?_,hs,hp⟩
  let v := fun n => (Fintype.equivFin (A 1)).symm (w n)
  have hb {i j : ℕ} (hij : i < j) :
      ((UnaryFactorization.block E v i j : A 1) : WithOne (A 1)) = WordFactorization.block (f ∘ w) i j :=
    SemigroupFactorization.coe_block v hij
  constructor
  · rintro ⟨x,y,cut,⟨a,e,rfl,rfl,hacc⟩,hee,hae,hc,hpos,ha,he⟩
    refine ⟨a,e,cut,hacc,?_,?_,hc,hpos,?_,?_⟩
    · exact WithOne.coe_injective ((WithOne.coe_mul e e).trans hee)
    · exact WithOne.coe_injective ((WithOne.coe_mul a e).trans hae)
    · exact WithOne.coe_injective ((hb hpos).trans ha)
    · intro i;exact WithOne.coe_injective ((hb (hc (Nat.lt_succ_self _))).trans (he i))
  · rintro ⟨a,e,cut,hacc,hee,hae,hc,hpos,ha,he⟩
    refine ⟨(a : WithOne (A 1)),(e : WithOne (A 1)),cut,⟨a,e,rfl,rfl,hacc⟩,?_,?_,hc,hpos,?_,?_⟩
    · exact (WithOne.coe_mul e e).symm.trans (congrArg WithOne.coe hee)
    · exact (WithOne.coe_mul a e).symm.trans (congrArg WithOne.coe hae)
    · exact (hb hpos).symm.trans (congrArg WithOne.coe ha)
    · intro i;exact (hb (hc (Nat.lt_succ_self _))).symm.trans (congrArg WithOne.coe (he i))

private theorem power_self_mono : Monotone (fun n : ℕ => n^n+n+1) := by
  intro n m h
  by_cases hm : m = 0
  · have hn : n = 0 := by omega
    simp [hm,hn]
  · exact Nat.add_le_add_right (Nat.add_le_add
      ((Nat.pow_le_pow_left h n).trans (Nat.pow_le_pow_right (by omega) h)) h) 1

/--
---
conclusion: Lax369799.QuantitativeWordConditions.exists_condition
---
The linked-pair Buchi automaton records three monoid elements and two
flags. Apply the explicit determinization bound and then multiply by
the finite-word evaluator state count. Neither bound depends on the
values of the algebra's multiplication or accepting tables.
-/
theorem exists_condition {A : RankedSystems.RankedSet} (E : FiniteSyntacticAlgebra.Algebra A)
    (F : Set (A 0)) [Fintype (A 1)] [Fintype (A 0)]
    (u z : ℕ) (hu : Fintype.card (A 1) ≤ u) (hz : Fintype.card (A 0) ≤ z) :
    ∃ D : WordCondition (Fintype.card (A 1)) (Fintype.card (A 0)),
      (∀ w a,D.AcceptsFinite w a ↔ FiniteBranchWords.value E
        (w.map (Fintype.equivFin (A 1)).symm) ((Fintype.equivFin (A 0)).symm a) ∈ F) ∧
      (∀ w,D.AcceptsInfinite w ↔ AlgebraicOmegaWords.Accepts E F
        (fun n => (Fintype.equivFin (A 1)).symm (w n))) ∧
      D.states ≤ stateBound u z ∧ (∀ q,D.priority q ≤ priorityBound u) := by
  classical
  let eu := Fintype.equivFin (A 1)
  let ez := Fintype.equivFin (A 0)
  let f := fun (b : Fin (Fintype.card (A 1))) (a : Fin (Fintype.card (A 0))) =>
    ez (FiniteBranchWords.act E (eu.symm b) (ez.symm a))
  let G : Set (Fin (Fintype.card (A 0))) := {a | ez.symm a ∈ F}
  obtain ⟨D,hD,hs,hp⟩ := omega_regular (z := Fintype.card (A 0)) E F u hu
  refine ⟨CombinedWordCondition.combine D f G,?_,?_,?_,?_⟩
  · intro w a
    rw [CombinedWordCondition.finite_iff]
    have hv (w : List (Fin (Fintype.card (A 1)))) (a : Fin (Fintype.card (A 0))) :
        ez.symm (w.foldr f a) = FiniteBranchWords.value E (w.map eu.symm) (ez.symm a) := by
      induction w with
      | nil => rfl
      | cons b w ih =>
        simpa only [List.foldr_cons,List.map_cons,FiniteBranchWords.value,f,ez.symm_apply_apply]
          using congrArg (FiniteBranchWords.act E (eu.symm b)) ih
    exact Iff.of_eq (congrArg (· ∈ F) (hv w a))
  · intro w
    exact (CombinedWordCondition.infinite_iff D f G w).trans (hD w)
  · change Fintype.card (Fin D.states × FiniteBranchWords.State (Fin (Fintype.card (A 0)))) ≤ _
    simp only [Fintype.card_prod,Fintype.card_fin,FiniteBranchWords.State,Fintype.card_option,
      Fintype.card_sum,Fintype.card_fun]
    exact Nat.mul_le_mul hs (power_self_mono hz)
  · intro q
    exact hp _

end Lax369799Proofs.QuantitativeWordConditions
