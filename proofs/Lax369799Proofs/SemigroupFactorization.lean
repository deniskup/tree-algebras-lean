import Lax369799.SemigroupFactorization
import Lax369799Proofs.WordFactorization

namespace Lax369799Proofs.SemigroupFactorization
open Lax369799.SemigroupFactorization

private theorem coe_fold {M : Type} [Semigroup M] (l : List M) (a : M) :
    (↑(l.foldl (· * ·) a) : WithOne M) = ↑a * (l.map WithOne.coe).prod := by
  induction l generalizing a with
  | nil => simp
  | cons b l ih => simp only [List.foldl_cons, ih, WithOne.coe_mul, List.map_cons, List.prod_cons, mul_assoc]

private theorem coe_block {M : Type} [Semigroup M] (w : ℕ → M) {i j : ℕ} (h : i < j) :
    (↑(block w i j) : WithOne M) = Lax369799.WordFactorization.block (fun k => (w k : WithOne M)) i j := by
  have hj : j - i = (j - i - 1) + 1 := by omega
  rw [block, coe_fold, Lax369799.WordFactorization.block, hj, List.range'_succ]
  simp only [List.map_cons, List.prod_cons, List.map_map, Function.comp_def, Nat.add_sub_cancel]

/--
---
conclusion: Lax369799.SemigroupFactorization.factorization
---
Adjoin an identity to use monoid factorization. Its nonempty blocks lie
in the original semigroup. Thin the cuts to a recurrent vertex; stability
and idempotence are preserved when consecutive blocks are grouped.
-/
theorem factorization {M V : Type} [Semigroup M] [Finite M] [Finite V]
    (w : ℕ → M) (v : ℕ → V) :
    ∃ (cut : ℕ → ℕ) (a e : M) (r : V), StrictMono cut ∧ 0 < cut 0 ∧
      e * e = e ∧ a * e = a ∧ (∀ i, v (cut i) = r) ∧
      (∀ i, block w 0 (cut i) = a) ∧
      (∀ i j, i < j → block w (cut i) (cut j) = e) := by
  let : Finite (WithOne M) := inferInstanceAs (Finite (Option M))
  obtain ⟨c, a, e, hc, hpos, he, ha, hprefix, hblock⟩ :=
    WordFactorization.factorization (fun i => (w i : WithOne M))
  let a' := block w 0 (c 0)
  let e' := block w (c 0) (c 1)
  have hca : (a' : WithOne M) = a := (coe_block w hpos).trans (hprefix 0)
  have hce : (e' : WithOne M) = e := (coe_block w (hc (by decide : 0 < 1))).trans (hblock 0 1 (by decide))
  have he' : e' * e' = e' := WithOne.coe_injective (by rw [WithOne.coe_mul, hce, he])
  have ha' : a' * e' = a' := WithOne.coe_injective (by rw [WithOne.coe_mul, hca, hce, ha])
  obtain ⟨r, hr⟩ := InfiniteRamsey.infinite_color Set.univ Set.infinite_univ (fun i => v (c i))
  obtain ⟨f, hf, hfr⟩ := Nat.exists_strictMono_subsequence (fun N => by
    obtain ⟨i, hi, hN⟩ := hr.exists_gt N
    exact ⟨i, hN, hi.2⟩)
  have hp (i) : 0 < c i := hpos.trans_le (hc.monotone (Nat.zero_le i))
  refine ⟨fun i => c (f i), a', e', r, hc.comp hf, hp _, he', ha', hfr, ?_, ?_⟩
  · intro i
    apply WithOne.coe_injective
    exact (coe_block w (hp _)).trans ((hprefix _).trans hca.symm)
  · intro i j hij
    apply WithOne.coe_injective
    exact (coe_block w (hc (hf hij))).trans ((hblock _ _ (hf hij)).trans hce.symm)

end Lax369799Proofs.SemigroupFactorization
