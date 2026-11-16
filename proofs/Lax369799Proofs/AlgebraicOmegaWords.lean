import Lax369799.AlgebraicOmegaWords
import Lax369799Proofs.UnaryFactorization
import Lax369799Proofs.OmegaProducts
import Lax369799Proofs.LinkedPairFactorizations

namespace Lax369799Proofs.AlgebraicOmegaWords
set_option backward.isDefEq.respectTransparency false
open Lax369799
open RankedSystems (RankedSet)
open FiniteSyntacticAlgebra UnaryComposition UnaryFactorization UnfoldAutomata AlgebraicOmegaWords

/--
---
conclusion: Lax369799.AlgebraicOmegaWords.regular
---
Adjoin an identity to the finite unary semigroup. Nonempty interval
products still lie in the unary sort, so the linked-pair omega language
is exactly the language recognized by the finite-monoid construction.
-/
theorem regular {A : RankedSet} (E : Algebra A) (F : Set (A 0)) [Fintype (A 1)] {z : ℕ} :
    ∃ D : WordCondition (Fintype.card (A 1)) z, ∀ w, D.AcceptsInfinite w ↔
      Accepts E F (fun n => (Fintype.equivFin (A 1)).symm (w n)) := by
  classical
  letI : Semigroup (A 1) := { mul := product E, mul_assoc := UnaryComposition.associative E }
  letI : Finite (WithOne (A 1)) := inferInstanceAs (Finite (Option (A 1)))
  let f : Fin (Fintype.card (A 1)) → WithOne (A 1) := fun i =>
    ((Fintype.equivFin (A 1)).symm i : WithOne (A 1))
  let P : WithOne (A 1) → WithOne (A 1) → Prop := fun x y =>
    ∃ a e : A 1, (a : WithOne (A 1)) = x ∧ (e : WithOne (A 1)) = y ∧ E.eval 0 (lasso a e) ∈ F
  obtain ⟨D, hD⟩ := OmegaProducts.regular (z := z) f P
  refine ⟨D, fun w => (hD w).trans ?_⟩
  let v := fun n => (Fintype.equivFin (A 1)).symm (w n)
  have hb {i j : ℕ} (hij : i < j) :
      ((block E v i j : A 1) : WithOne (A 1)) = WordFactorization.block (f ∘ w) i j :=
    SemigroupFactorization.coe_block v hij
  constructor
  · rintro ⟨x, y, cut, ⟨a, e, rfl, rfl, hacc⟩, hee, hae, hc, hpos, ha, he⟩
    refine ⟨a, e, cut, hacc, ?_, ?_, hc, hpos, ?_, ?_⟩
    · exact WithOne.coe_injective ((WithOne.coe_mul e e).trans hee)
    · exact WithOne.coe_injective ((WithOne.coe_mul a e).trans hae)
    · exact WithOne.coe_injective ((hb hpos).trans ha)
    · intro i
      exact WithOne.coe_injective ((hb (hc (Nat.lt_succ_self _))).trans (he i))
  · rintro ⟨a, e, cut, hacc, hee, hae, hc, hpos, ha, he⟩
    refine ⟨(a : WithOne (A 1)), (e : WithOne (A 1)), cut, ⟨a, e, rfl, rfl, hacc⟩,
      ?_, ?_, hc, hpos, ?_, ?_⟩
    · exact (WithOne.coe_mul e e).symm.trans (congrArg WithOne.coe hee)
    · exact (WithOne.coe_mul a e).symm.trans (congrArg WithOne.coe hae)
    · exact (hb hpos).symm.trans (congrArg WithOne.coe ha)
    · intro i
      exact (hb (hc (Nat.lt_succ_self _))).symm.trans (congrArg WithOne.coe (he i))

/--
---
conclusion: Lax369799.AlgebraicOmegaWords.recurrent_factorization
---
Thin the factorization to a recurrent graph vertex. Nonempty monoid
products are still unary values, so thinning preserves the original
accepting linked pair.
-/
theorem recurrent_factorization {A : RankedSet} (E : Algebra A) (F : Set (A 0))
    {V : Type} [Finite V] (w : ℕ → A 1) (v : ℕ → V) (h : Accepts E F w) :
    ∃ (a e : A 1) (c : ℕ → ℕ) (r : V), E.eval 0 (lasso a e) ∈ F ∧
      product E e e = e ∧ product E a e = a ∧ StrictMono c ∧ 0 < c 0 ∧
      (∀ i, v (c i) = r) ∧ (∀ i, block E w 0 (c i) = a) ∧
      (∀ i j, i < j → block E w (c i) (c j) = e) := by
  letI : Semigroup (A 1) := { mul := product E, mul_assoc := UnaryComposition.associative E }
  obtain ⟨a, e, c, hacc, hee, hae, hc, hpos, ha, he⟩ := h
  have hb {i j : ℕ} (hij : i < j) :
      (↑(block E w i j) : WithOne (A 1)) =
        WordFactorization.block (fun n => (w n : WithOne (A 1))) i j :=
    SemigroupFactorization.coe_block w hij
  obtain ⟨d, r, hd, hposd, hvr, hp, hblocks⟩ := LinkedPairFactorizations.thin
    (fun n => (w n : WithOne (A 1))) v (a : WithOne (A 1)) (e : WithOne (A 1)) c
    ((WithOne.coe_mul e e).symm.trans (congrArg WithOne.coe hee))
    ((WithOne.coe_mul a e).symm.trans (congrArg WithOne.coe hae)) hc hpos
    ((hb hpos).symm.trans (congrArg WithOne.coe ha))
    (fun i => (hb (hc (Nat.lt_succ_self _))).symm.trans (congrArg WithOne.coe (he i)))
  refine ⟨a, e, d, r, hacc, hee, hae, hd, hposd, hvr, ?_, ?_⟩
  · intro i
    exact WithOne.coe_injective ((hb (hposd.trans_le (hd.monotone (Nat.zero_le _)))).trans (hp i))
  · intro i j hij
    exact WithOne.coe_injective ((hb (hd hij)).trans (hblocks i j hij))

end Lax369799Proofs.AlgebraicOmegaWords
