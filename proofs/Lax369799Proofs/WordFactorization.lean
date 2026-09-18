import Lax369799.WordFactorization
import Lax369799Proofs.InfiniteRamsey
import Mathlib.Data.Finite.Prod

namespace Lax369799Proofs.WordFactorization
open Lax369799.WordFactorization

theorem block_append {M : Type} [Monoid M] (w : ℕ → M) {i j k : ℕ}
    (hij : i ≤ j) (hjk : j ≤ k) : block w i k = block w i j * block w j k := by
  have he : List.range' i (k - i) = List.range' i (j - i) ++ List.range' j (k - j) := by
    have h := @List.range'_append i (j - i) (k - j) 1
    have h1 : i + 1 * (j - i) = j := by omega
    have h2 : j - i + (k - j) = k - i := by omega
    rw [h1, h2] at h
    exact h.symm
  simp only [block, he, List.map_append, List.prod_append]

/--
---
conclusion: Lax369799.WordFactorization.factorization
---
Color each increasing pair by its interval product and its left prefix
product. Ramsey homogeneity fixes both. Concatenating two homogeneous
intervals proves idempotence, and appending one to a prefix proves stability.
-/
theorem factorization {M : Type} [Monoid M] [Finite M] (w : ℕ → M) :
    ∃ (cut : ℕ → ℕ) (a e : M), StrictMono cut ∧ 0 < cut 0 ∧
      e * e = e ∧ a * e = a ∧
      (∀ i, block w 0 (cut i) = a) ∧
      (∀ i j, i < j → block w (cut i) (cut j) = e) := by
  obtain ⟨f, c, hf, hc⟩ := InfiniteRamsey.pairs (fun i j => (block w i j, block w 0 i))
  let cut := fun i => f (i + 1)
  have hcut : StrictMono cut := hf.comp (fun _ _ h => Nat.add_lt_add_right h 1)
  have hpos : 0 < cut 0 := lt_of_le_of_lt (Nat.zero_le (f 0)) (hf (by decide : 0 < 1))
  have hp (i) : block w 0 (cut i) = c.2 :=
    congrArg Prod.snd (hc (i + 1) (i + 2) (by omega))
  have hb (i j) (h : i < j) : block w (cut i) (cut j) = c.1 :=
    congrArg Prod.fst (hc (i + 1) (j + 1) (by omega))
  have hi := block_append w (hcut (by decide : 0 < 1)).le (hcut (by decide : 1 < 2)).le
  rw [hb 0 2 (by decide), hb 0 1 (by decide), hb 1 2 (by decide)] at hi
  have ha := block_append w (Nat.zero_le (cut 0)) (hcut (by decide : 0 < 1)).le
  rw [hp 0, hp 1, hb 0 1 (by decide)] at ha
  exact ⟨cut, c.2, c.1, hcut, hpos, hi.symm, ha.symm, hp, hb⟩

end Lax369799Proofs.WordFactorization
