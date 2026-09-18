import Lax369799.PeriodicPaths
import Lax369799Proofs.WordParity

namespace Lax369799Proofs.PeriodicPaths
open Lax369799.PeriodicPaths Lax369799.WordParity

private def index (i j n : ℕ) : ℕ := if n < i then n else i + (n - i) % (j - i)

private theorem index_zero (i j : ℕ) : index i j 0 = 0 := by
  by_cases hi : 0 < i
  · simp [index, hi]
  · have hi : i = 0 := by omega
    simp [index, hi]

private theorem index_bounds {i j n : ℕ} (hij : i < j) (hn : i ≤ n) :
    i ≤ index i j n ∧ index i j n < j := by
  have hp : 0 < j - i := by omega
  have hm := Nat.mod_lt (n - i) hp
  simp only [index, if_neg (by omega : ¬n < i)]
  omega

private theorem index_succ {i j : ℕ} (hij : i < j) (n : ℕ) :
    index i j (n + 1) = index i j n + 1 ∨
      index i j n + 1 = j ∧ index i j (n + 1) = i := by
  by_cases hn : n < i
  · have hn' : n + 1 ≤ i := by omega
    by_cases hh : n + 1 < i
    · simp [index, hn, hh]
    · have he : n + 1 = i := by omega
      simp [index, hn, he]
  · have hn' : ¬ n + 1 < i := by omega
    simp only [index, if_neg hn, if_neg hn']
    have hp : 0 < j - i := by omega
    have he : n + 1 - i = n - i + 1 := by omega
    rw [he]
    have hm := Nat.mod_lt (n - i) hp
    have hmod : (n - i + 1) % (j - i) = ((n - i) % (j - i) + 1) % (j - i) := by
      simp only [Nat.add_mod, Nat.mod_mod]
    rw [hmod]
    by_cases hlt : (n - i) % (j - i) + 1 < j - i
    · rw [Nat.mod_eq_of_lt hlt]
      exact Or.inl (by omega)
    · have heq : (n - i) % (j - i) + 1 = j - i := by omega
      rw [heq, Nat.mod_self]
      exact Or.inr ⟨by omega, by omega⟩

private theorem index_period {i j : ℕ} (_hij : i < j) (n : ℕ) (hn : i ≤ n) :
    index i j (n + (j - i)) = index i j n := by
  have hn' : ¬n + (j - i) < i := by omega
  simp only [index, if_neg hn', if_neg (by omega : ¬n < i)]
  have he : n + (j - i) - i = (n - i) + (j - i) := by omega
  rw [he, Nat.add_mod_right]

private theorem index_return {i j : ℕ} (_hij : i < j) (m : ℕ) :
    index i j (i + m * (j - i)) = i := by
  have hn : ¬ i + m * (j - i) < i := by omega
  simp [index, hn]

/--
---
conclusion: Lax369799.PeriodicPaths.periodic_witness
---
Choose two equal states of least recurring priority after all lower
priorities have disappeared. Retain the prefix and repeat the intervening
nonempty segment. Its minimum priority recurs and no lower one recurs.
-/
theorem periodic_witness {Q : Type} [Finite Q] (R : Q → Q → Prop)
    (priority : Q → ℕ) (r : ℕ → Q) (hr : ∀ n, R (r n) (r (n + 1)))
    (c : ℕ) (hc : LeastRecurring (fun n => priority (r n)) c) :
    ∃ s : ℕ → Q, s 0 = r 0 ∧ (∀ n, R (s n) (s (n + 1))) ∧
      UltimatelyPeriodic s ∧ LeastRecurring (fun n => priority (s n)) c := by
  obtain ⟨i, j, _, hij, he, hpi, hp⟩ := WordParity.minimum_cycle priority r c hc 0
  let s := fun n => r (index i j n)
  refine ⟨s, congrArg r (index_zero i j), ?_, ?_, ?_, ?_⟩
  · intro n
    change R (r (index i j n)) (r (index i j (n + 1)))
    rcases index_succ hij n with hn | ⟨hn, hn'⟩
    · rw [hn]
      exact hr (index i j n)
    · rw [hn', he]
      have h := hr (index i j n)
      rw [hn] at h
      exact h
  · exact ⟨i, j - i, by omega, fun n hn => congrArg r (index_period hij n hn)⟩
  · intro N
    refine ⟨i + N * (j - i), ?_, ?_⟩
    · have hp : 1 ≤ j - i := by omega
      have hN := Nat.mul_le_mul_left N hp
      omega
    · change priority (r (index i j _)) = c
      rw [index_return hij]
      exact hpi
  · intro b hb
    refine ⟨i, ?_⟩
    intro n hn
    have hbounds := index_bounds hij hn
    have hpn := hp _ hbounds.1 hbounds.2.le
    change priority (r (index i j n)) ≠ b
    omega

/--
---
conclusion: Lax369799.PeriodicPaths.periodic_test
---
An arbitrary path and its periodic witness have the same least recurring
priority. Acceptance of every periodic path therefore implies acceptance
of every path from the initial vertex.
-/
theorem periodic_test {Q : Type} [Finite Q] (R : Q → Q → Prop)
    (priority : Q → ℕ) (q : Q) :
    (∀ r : ℕ → Q, r 0 = q → (∀ n, R (r n) (r (n + 1))) → UltimatelyPeriodic r →
      ∃ c, Even c ∧ LeastRecurring (fun n => priority (r n)) c) ↔
    (∀ r : ℕ → Q, r 0 = q → (∀ n, R (r n) (r (n + 1))) →
      ∃ c, Even c ∧ LeastRecurring (fun n => priority (r n)) c) := by
  constructor
  · intro h r hq hr
    obtain ⟨c, hc, _⟩ := WordParity.least_recurring priority r
    obtain ⟨s, hs, hsR, hsp, hsc⟩ := periodic_witness R priority r hr c hc
    obtain ⟨d, hd, hsd⟩ := h s (hs.trans hq) hsR hsp
    obtain ⟨e, _, he⟩ := WordParity.least_recurring priority s
    have hdc : d = c := (he d hsd).trans (he c hsc).symm
    exact ⟨c, hdc ▸ hd, hc⟩
  · exact fun h r hq hr _ => h r hq hr

end Lax369799Proofs.PeriodicPaths
