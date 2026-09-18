import Lax369799.WordParity
import Lax369799Proofs.InfiniteRamsey
import Mathlib.Data.Finset.Lattice.Fold

namespace Lax369799Proofs.WordParity
open Lax369799.WordParity

private theorem unique (p : ℕ → ℕ) {c d : ℕ} (hc : LeastRecurring p c)
    (hd : LeastRecurring p d) : c = d := by
  have hle : ∀ {a b}, LeastRecurring p a → LeastRecurring p b → a ≤ b := by
    intro a b ha hb
    by_contra h
    obtain ⟨N, hN⟩ := ha.2 b (by omega)
    obtain ⟨n, hn, he⟩ := hb.1 N
    exact hN n hn he
  exact Nat.le_antisymm (hle hc hd) (hle hd hc)

/--
---
conclusion: Lax369799.WordParity.least_recurring
---
An infinite color class supplies a recurring priority. Choose the least
such natural number; every smaller priority has a last occurrence.
-/
theorem least_recurring {Q : Type} [Finite Q] (priority : Q → ℕ) (r : ℕ → Q) :
    ∃! c, LeastRecurring (fun n => priority (r n)) c := by
  classical
  obtain ⟨q, hq⟩ := InfiniteRamsey.infinite_color Set.univ Set.infinite_univ r
  have hex : ∃ c, Recurrent (fun n => priority (r n)) c := by
    refine ⟨priority q, ?_⟩
    intro N
    obtain ⟨n, hn, hN⟩ := hq.exists_gt N
    exact ⟨n, hN.le, congrArg priority hn.2⟩
  let c := Nat.find hex
  have hc : LeastRecurring (fun n => priority (r n)) c := by
    refine ⟨Nat.find_spec hex, ?_⟩
    intro b hb
    have hn : ¬ Recurrent (fun n => priority (r n)) b := Nat.find_min hex hb
    unfold Recurrent at hn
    push Not at hn
    exact hn
  exact ⟨c, hc, fun d hd => unique _ hd hc⟩

/--
---
conclusion: Lax369799.WordParity.recurrent_shift
---
Shift witnesses forward, or choose a witness beyond the omitted prefix
and subtract its length.
-/
theorem recurrent_shift (p : ℕ → ℕ) (c k : ℕ) :
    Recurrent (fun n => p (n + k)) c ↔ Recurrent p c := by
  constructor
  · intro h N
    obtain ⟨n, hn, he⟩ := h N
    exact ⟨n + k, by omega, he⟩
  · intro h N
    obtain ⟨n, hn, he⟩ := h (N + k)
    refine ⟨n - k, by omega, ?_⟩
    have hnk : n - k + k = n := by omega
    simpa only [hnk] using he

private theorem eventually_lower_bound (p : ℕ → ℕ) (c : ℕ) (hc : LeastRecurring p c) :
    ∃ N, ∀ n, N ≤ n → c ≤ p n := by
  classical
  choose N hN using fun b : Fin c => hc.2 b.val b.isLt
  refine ⟨Finset.univ.sup N, ?_⟩
  intro n hn
  by_contra h
  let b : Fin c := ⟨p n, by omega⟩
  have hbound : N b ≤ Finset.univ.sup N := Finset.le_sup (Finset.mem_univ b)
  exact hN b n (hbound.trans hn) rfl

/--
---
conclusion: Lax369799.WordParity.minimum_cycle
---
Discard the finitely many occurrences of smaller priorities. Among the
infinitely many occurrences of the least recurring priority, some state
recurs infinitely often. Choose two occurrences after the given bound.
-/
theorem minimum_cycle {Q : Type} [Finite Q] (priority : Q → ℕ) (r : ℕ → Q)
    (c : ℕ) (hc : LeastRecurring (fun n => priority (r n)) c) (N : ℕ) :
    ∃ i j, N ≤ i ∧ i < j ∧ r i = r j ∧ priority (r i) = c ∧
      ∀ k, i ≤ k → k ≤ j → c ≤ priority (r k) := by
  have hs : {n | priority (r n) = c}.Infinite := Set.infinite_of_forall_exists_gt (fun K => by
    obtain ⟨n, hn, he⟩ := hc.1 (K + 1)
    exact ⟨n, he, by omega⟩)
  obtain ⟨q, hq⟩ := InfiniteRamsey.infinite_color _ hs r
  obtain ⟨K, hK⟩ := eventually_lower_bound _ c hc
  obtain ⟨i, hi, hNi⟩ := hq.exists_gt (max N K)
  obtain ⟨j, hj, hij⟩ := hq.exists_gt i
  exact ⟨i, j, by omega, hij, hi.2.trans hj.2.symm, hi.1,
    fun k hik _ => hK k (by omega)⟩

/--
---
conclusion: Lax369799.WordParity.acceptance_iff
---
The parity condition is exactly evenness of the unique least recurring
priority of the word automaton's run.
-/
theorem acceptance_iff {u z : ℕ} (D : Lax369799.UnfoldAutomata.WordCondition u z)
    (w : ℕ → Fin u) (c : ℕ)
    (hc : LeastRecurring (fun n => D.priority (D.run w n)) c) :
    D.AcceptsInfinite w ↔ Even c := by
  constructor
  · rintro ⟨d, hd, hr, hl⟩
    exact unique _ ⟨hr, hl⟩ hc ▸ hd
  · intro he
    exact ⟨c, he, hc.1, hc.2⟩

end Lax369799Proofs.WordParity
