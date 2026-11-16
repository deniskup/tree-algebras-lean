import Lax369799.LinkedPairFactorizations
import Lax369799Proofs.OmegaProducts

namespace Lax369799Proofs.LinkedPairFactorizations
open Lax369799.WordFactorization Lax369799.OmegaProducts

private theorem prefix_blocks {M : Type} [Monoid M] {w : ℕ → M}
    {a e : M} {c : ℕ → ℕ} (hc : StrictMono c) (hae : a * e = a)
    (ha : block w 0 (c 0) = a) (he : ∀ i, block w (c i) (c (i + 1)) = e) :
    ∀ i, block w 0 (c i) = a := by
  intro i
  induction i with
  | zero => exact ha
  | succ i ih =>
    rw [WordFactorization.block_append w (Nat.zero_le _) (hc (Nat.lt_succ_self _)).le,
      ih, he i, hae]

private theorem union_blocks {M : Type} [Monoid M] {w : ℕ → M}
    {e : M} {c : ℕ → ℕ} (hc : StrictMono c) (hee : e * e = e)
    (he : ∀ i, block w (c i) (c (i + 1)) = e) :
    ∀ i j, i < j → block w (c i) (c j) = e := by
  have h (i k : ℕ) : block w (c i) (c (i + k + 1)) = e := by
    induction k with
    | zero => simpa using he i
    | succ k ih =>
      rw [show i + (k + 1) + 1 = (i + k + 1) + 1 from by omega]
      rw [WordFactorization.block_append w (hc.monotone (by omega : i ≤ i + k + 1))
        (hc (Nat.lt_succ_self _)).le, ih, he, hee]
  intro i j hij
  have hlen : i + (j - i - 1) + 1 = j := by omega
  simpa only [hlen] using h i (j - i - 1)

theorem thin {M V : Type} [Monoid M] [Finite V] (w : ℕ → M) (v : ℕ → V)
    (a e : M) (c : ℕ → ℕ) (hee : e * e = e) (hae : a * e = a)
    (hc : StrictMono c) (hpos : 0 < c 0) (ha : block w 0 (c 0) = a)
    (he : ∀ i, block w (c i) (c (i + 1)) = e) :
    ∃ (d : ℕ → ℕ) (r : V), StrictMono d ∧ 0 < d 0 ∧ (∀ i, v (d i) = r) ∧
      (∀ i, block w 0 (d i) = a) ∧
      (∀ i j, i < j → block w (d i) (d j) = e) := by
  have hp := prefix_blocks hc hae ha he
  have hb := union_blocks hc hee he
  obtain ⟨r, hr⟩ := InfiniteRamsey.infinite_color Set.univ Set.infinite_univ (fun i => v (c i))
  obtain ⟨g, hg, hgr⟩ := Nat.exists_strictMono_subsequence (fun N => by
    obtain ⟨i, hi, hN⟩ := hr.exists_gt N
    exact ⟨i, hN, hi.2⟩)
  refine ⟨fun i => c (g i), r, hc.comp hg,
    hpos.trans_le (hc.monotone (Nat.zero_le _)), hgr, fun i => hp (g i), ?_⟩
  intro i j hij
  exact hb _ _ (hg hij)

/--
---
conclusion: Lax369799.LinkedPairFactorizations.recurrent_factorization
---
Absorb earlier blocks into each prefix, combine blocks by idempotence,
and thin to a recurrent vertex using the infinite pigeonhole principle.
-/
theorem recurrent_factorization {M V : Type} [Monoid M] [Finite V] {u : ℕ}
    (f : Fin u → M) (P : M → M → Prop) (w : ℕ → Fin u) (v : ℕ → V)
    (h : Accepts f P w) :
    ∃ (a e : M) (c : ℕ → ℕ) (r : V), P a e ∧ e * e = e ∧ a * e = a ∧
      StrictMono c ∧ 0 < c 0 ∧ (∀ i, v (c i) = r) ∧
      (∀ i, block (f ∘ w) 0 (c i) = a) ∧
      (∀ i j, i < j → block (f ∘ w) (c i) (c j) = e) := by
  obtain ⟨a, e, c, hP, hee, hae, hc, hpos, ha, he⟩ := h
  obtain ⟨d, r, hd, hposd, hvr, hp, hb⟩ := thin (f ∘ w) v a e c hee hae hc hpos ha he
  exact ⟨a, e, d, r, hP, hee, hae, hd, hposd, hvr, hp, hb⟩

end Lax369799Proofs.LinkedPairFactorizations
