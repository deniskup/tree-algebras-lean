import Lax369799.QuantitativeProfiles
import Lax369799Proofs.QuantitativeRecognition
import Lax369799Proofs.BoundedProfileRefinement
import Mathlib.Data.Finite.Sigma
import Mathlib.Algebra.Order.BigOperators.Group.Finset

set_option backward.isDefEq.respectTransparency false
namespace Lax369799Proofs.QuantitativeProfiles
open Lax369799
open RankedSystems Algebras FinitePresentations FiniteProfiles Resolutions
open Lax369799.QuantitativeRecognition Lax369799.QuantitativeProfiles

private theorem regularization {A : RankedSet} (L : Language A) (hL : UnfoldInvariantLanguage L)
    (f : ℕ → ℕ) (hrec : Bound f L) :
    ∃ (B : RankedSet) (E : Algebra B) (η : RankedMap A B) (F : Set (B 0)),
      RankwiseFinite B ∧ UnfoldInvariant E ∧ Recognizes E η F L ∧ ∀ k,Nat.card (B k) ≤ f k := by
  obtain ⟨B,E,η,F,hB,hrec,hb⟩ := hrec
  obtain ⟨G,hG⟩ := GeneratedAlgebra.algebra E η
  let F' : Set (GeneratedAlgebra.Carrier E η 0) := {b | b.val ∈ F}
  obtain ⟨Q,hQ⟩ := PolynomialQuotient.algebra G F'
  let C := PolynomialQuotient.Carrier G F'
  refine ⟨C,Q,(fun n a => PolynomialQuotient.classMap G F' n
    (GeneratedAlgebra.letter E η n a)),PolynomialQuotient.Accepting G F',
    PolynomialQuotient.finite_carrier G F' (GeneratedAlgebra.finite_carrier E η hB),
    PolynomialUnfolding.quotient_unfold_invariant G F'
      (Regularization.generated_closed_invariant E η G hG F L hL hrec) Q hQ,
    PolynomialQuotient.recognition G F' Q hQ (GeneratedAlgebra.letter E η) L
      (GeneratedAlgebra.recognition E η G hG F L hrec),?_⟩
  intro k
  let : Finite (B k) := hB k
  let : Finite (GeneratedAlgebra.Carrier E η k) := GeneratedAlgebra.finite_carrier E η hB k
  have hq := Nat.card_le_card_of_surjective (PolynomialQuotient.classMap G F' k)
    (fun x => Quot.exists_rep x)
  have hs := Nat.card_le_card_of_injective
    (fun x : GeneratedAlgebra.Carrier E η k => x.val) Subtype.val_injective
  exact hq.trans (hs.trans (hb k))

private theorem entry_card {B : RankedSet} (hB : RankwiseFinite B) (f : ℕ → ℕ)
    (hf : ∀ k,Nat.card (B k) ≤ f k) (bound b n : ℕ) (hb : b ≤ bound) :
    Nat.card (BoundedProfiles.BoundedEntry B b n) ≤ entryBound f bound n := by
  classical
  let : ∀ k,Finite (B k) := hB
  let X := (k : Fin (n*bound+1)) × B k.val × (Fin k.val → Fin n)
  let g : BoundedProfiles.BoundedEntry B b n → X := fun e =>
    ⟨⟨e.val.1,by
      have hh := BoundedProfiles.small_rank_bound e.val.2.2 e.property
      exact Nat.lt_succ_of_le (hh.trans (Nat.mul_le_mul_left n hb))⟩,e.val.2⟩
  have hg : Function.Injective g := by
    intro a b h
    exact Subtype.ext (congrArg (fun x : X => (⟨x.1.val,x.2⟩ : ProfileEntry B n)) h)
  have hc := Nat.card_le_card_of_injective g hg
  have hx : Nat.card X = ∑ k : Fin (n*bound+1), Nat.card (B k.val)*n^k.val := by
    rw [Nat.card_sigma]
    apply Finset.sum_congr rfl
    intro k _
    rw [Nat.card_prod,Nat.card_fun]
    simp
  have hs : (∑ k : Fin (n*bound+1), Nat.card (B k.val)*n^k.val) ≤
      ∑ k : Fin (n*bound+1), f k.val*n^k.val :=
    Finset.sum_le_sum (fun k _ => Nat.mul_le_mul_right _ (hf k.val))
  have he : (∑ k : Fin (n*bound+1),f k.val*n^k.val) = entryBound f bound n := by
    simpa only [entryBound] using (Fin.sum_univ_eq_sum_range (fun k => f k*n^k) (n*bound+1))
  exact hc.trans (hx.le.trans (hs.trans_eq he))

private theorem quotient_card {A B : RankedSet} (hB : RankwiseFinite B) (f : ℕ → ℕ)
    (hf : ∀ k,Nat.card (B k) ≤ f k) (bound b n : ℕ) (hb : b ≤ bound)
    (ρ : ∀ k,System A k → B k) :
    Nat.card (Quot (@BoundedProfileEquivalent A B b ρ n)) ≤ 2 ^ (2*entryBound f bound n) := by
  classical
  let : Finite (BoundedProfiles.BoundedEntry B b n) := BoundedProfiles.small_entry_finite hB b n
  let E := BoundedProfiles.BoundedEntry B b n
  let g : Quot (@BoundedProfileEquivalent A B b ρ n) → Set E × Set E :=
    Quot.lift (BoundedProfiles.profileCode b ρ)
      (fun S T h => (BoundedProfiles.code_eq_iff b ρ S T).mpr h)
  have hg : Function.Injective g := by
    intro a c
    induction a using Quot.inductionOn with
    | h S =>
      induction c using Quot.inductionOn with
      | h T => exact fun h => Quot.sound ((BoundedProfiles.code_eq_iff b ρ S T).mp h)
  have hc := Nat.card_le_card_of_injective g hg
  let : Fintype E := Fintype.ofFinite E
  have he : Nat.card (Set E × Set E) = 2 ^ (2*Nat.card E) := by
    simp [Nat.card_eq_fintype_card,Nat.two_mul,Nat.pow_add]
  exact hc.trans (he.le.trans (Nat.pow_le_pow_right (by decide)
    (Nat.mul_le_mul_left 2 (entry_card hB f hf bound b n hb))))

/--
---
conclusion: Lax369799.QuantitativeProfiles.syntactic_bound
---
Regularization is a subalgebra followed by a quotient, so it cannot
increase a sort. Bounded entries have rank at most n times the fibre
bound. Initial and root profiles give two subsets of the explicitly
bounded entry type; their quotient surjects onto the contextual classes.
-/
theorem syntactic_bound {A : RankedSet} (L : Language A) (hL : UnfoldInvariantLanguage L)
    (f : ℕ → ℕ) (hrec : Bound f L) (n : ℕ) :
    Nat.card (FiniteContextualOrder.Carrier (FiniteAcceptance.Accepting L) n) ≤ quotientBound f n := by
  classical
  obtain ⟨B,E,η,F,hB,hE,hr,hf⟩ := regularization L hL f hrec
  let : Finite (B 1) := hB 1
  let b := Nat.card (B 1)+1
  let ρ := fun k R => E.eval k (relabelSystem η R)
  let : Finite (Quot (@BoundedProfileEquivalent A B b ρ n)) :=
    BoundedProfiles.bounded_profile_finite hB b ρ n
  let g : Quot (@BoundedProfileEquivalent A B b ρ n) →
      FiniteContextualOrder.Carrier (FiniteAcceptance.Accepting L) n :=
    Quot.lift (fun S => Quot.mk _ S)
      (fun S T h => Quot.sound (BoundedProfileRefinement.refines E hE η F L hr S T h))
  have hg : Function.Surjective g := by
    intro a
    induction a using Quot.inductionOn with
    | h S => exact ⟨Quot.mk _ S,rfl⟩
  exact (Nat.card_le_card_of_surjective g hg).trans
    (quotient_card hB f hf (f 1+1) b n (Nat.add_le_add_right (hf 1) 1) ρ)

end Lax369799Proofs.QuantitativeProfiles
