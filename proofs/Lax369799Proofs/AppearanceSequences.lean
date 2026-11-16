/-
Adapted from the Lean ancillary files of Bojańczyk, Casares, Manthe and
Parys, arXiv:2611.10136v1 (2026), with incorporation authorized by the user.
Original module: BorelMSO.Emptiness.LARSeq.
Changes: Archive module paths and namespaces; port to the pinned toolchain.
See external-proofs.json for source provenance.
-/
import Mathlib.Tactic.Ring
import Lax369799Proofs.AppearanceRecords
import Lax369799Proofs.ParityGames

/-!
# The latest appearance record turns a Muller condition into a parity condition

Given a sequence `qs : ℕ → Q` of states of a finite state space and the latest appearance
record along it (`Lax369799Proofs.WordAutomata/Basic/LAR.lean`), reading the state `q` in the record `r`
produces the priority

* `2 * h + 2` if the set `S` of the `h + 1` most recently read states belongs to the
  acceptance family, and `2 * h + 1` otherwise,

where `h = r q` is the rank of `q` in the record, i.e. the number of states read more
recently than `q`.

The main result `Lax369799Proofs.WordAutomata.LARSeq.exists_even_maxInfOften_iff` states that the maximal
priority produced infinitely often is even if and only if the set of states occurring
infinitely often in `qs` belongs to the acceptance family.  This is the classical
translation of a Muller condition into a parity condition.
-/

namespace Lax369799Proofs.WordAutomata

namespace LARSeq

open LAR FinGame

variable {Q : Type} [Fintype Q] [DecidableEq Q] [Nonempty Q]

/-- The rank functions, i.e. latest appearance records, of a sequence of states: `recSeq n`
is the record before reading `qs n`. -/
def recSeq (qs : ℕ → Q) (r0 : Q → Fin (card Q)) : ℕ → (Q → Fin (card Q))
  | 0 => r0
  | n + 1 => upd (qs n) (recSeq qs r0 n)

/-- The priority produced by reading the state `q` in the record `r`. -/
def prioOf (acc : Set (Set Q)) [DecidablePred (· ∈ acc)] (q : Q) (r : Q → Fin (card Q)) : ℕ :=
  if {x : Q | ((upd q r x : Fin (card Q)) : ℕ) ≤ ((r q : Fin (card Q)) : ℕ)} ∈ acc
    then 2 * ((r q : Fin (card Q)) : ℕ) + 2
    else 2 * ((r q : Fin (card Q)) : ℕ) + 1

/-- The shifted sequence, in the indexing convention of `Lax369799Proofs.WordAutomata/Basic/LAR.lean` (where the
state of index `0` is not read). -/
def shiftSeq (qs : ℕ → Q) : ℕ → Q := fun k => qs (k - 1)

theorem recSeq_eq_rank (qs : ℕ → Q) (r0 : Q → Fin (card Q)) (n : ℕ) :
    recSeq qs r0 n = rank (shiftSeq qs) r0 n := by
  induction n with
  | zero => rfl
  | succ k ih =>
      show upd (qs k) (recSeq qs r0 k) = upd (shiftSeq qs (k + 1)) (rank (shiftSeq qs) r0 k)
      rw [ih]
      rfl

omit [Fintype Q] [DecidableEq Q] [Nonempty Q] in
theorem infinite_shift_iff (qs : ℕ → Q) (x : Q) :
    {n | shiftSeq qs n = x}.Infinite ↔ {n | qs n = x}.Infinite := by
  constructor
  · intro h hfin
    have hsub : {n | shiftSeq qs n = x} ⊆ insert 0 ((fun n => n + 1) '' {n | qs n = x}) := by
      intro n hn
      rcases Nat.eq_zero_or_pos n with rfl | hpos
      · exact Set.mem_insert _ _
      · refine Set.mem_insert_of_mem _ ⟨n - 1, ?_, ?_⟩
        · have hx : qs (n - 1) = x := hn
          exact hx
        · show n - 1 + 1 = n
          omega
    exact h (Set.Finite.subset ((hfin.image _).insert 0) hsub)
  · intro h hfin
    have himg : ((fun n => n + 1) '' {n | qs n = x}).Infinite :=
      h.image (Set.injOn_of_injective (fun a b hab => by omega))
    refine himg ?_
    refine Set.Finite.subset hfin ?_
    rintro _ ⟨n, hn, rfl⟩
    show qs (n + 1 - 1) = x
    simpa using hn

omit [DecidableEq Q] [Nonempty Q] in
theorem infSetF_shift (qs : ℕ → Q) : infSetF (shiftSeq qs) = infSetF qs := by
  ext x
  rw [mem_infSetF, mem_infSetF]
  exact infinite_shift_iff qs x

omit [DecidableEq Q] [Nonempty Q] in
theorem coe_infSetF (qs : ℕ → Q) :
    ↑(infSetF qs) = {q : Q | {n | qs n = q}.Infinite} := by
  ext x
  simp only [Finset.mem_coe, Set.mem_setOf_eq]
  exact mem_infSetF qs

/-! ### The main computation -/

section Main

variable (acc : Set (Set Q)) [DecidablePred (· ∈ acc)] (qs : ℕ → Q) {r0 : Q → Fin (card Q)}

/-- The set of states of small rank is the set of states occurring infinitely often, and the
state that is read belongs to it: this holds from some time on. -/
theorem exists_good_time (hr0 : Function.Injective r0) :
    ∃ N : ℕ, (∀ n, N ≤ n → ∀ x : Q,
        (((recSeq qs r0 n x : Fin (card Q)) : ℕ) < (infSetF qs).card ↔ x ∈ infSetF qs)) ∧
      (∀ n, N ≤ n → qs n ∈ infSetF qs) := by
  classical
  obtain ⟨N₁, hN₁⟩ := eventually_rank_lt_card (shiftSeq qs) r0 hr0
  obtain ⟨N₀, hN₀⟩ := exists_eventually_mem_infSetF (shiftSeq qs)
  refine ⟨max N₁ N₀, fun n hn x => ?_, fun n hn => ?_⟩
  · have h := hN₁ n (le_trans (le_max_left _ _) hn) x
    rw [infSetF_shift] at h
    rw [recSeq_eq_rank]
    exact h
  · have hmem := hN₀ (n + 1) (by omega)
    rw [infSetF_shift] at hmem
    have : shiftSeq qs (n + 1) = qs n := rfl
    rwa [this] at hmem

variable {acc qs}

/-- The set of states at least as recent as the state that is read, when the latter has the
largest rank among the states occurring infinitely often, is exactly that set of states. -/
theorem recent_set_eq {n : ℕ}
    (hrank : ∀ x : Q, (((recSeq qs r0 n x : Fin (card Q)) : ℕ) < (infSetF qs).card ↔
      x ∈ infSetF qs))
    (hread : qs n ∈ infSetF qs)
    (hmax : ((recSeq qs r0 n (qs n) : Fin (card Q)) : ℕ) = (infSetF qs).card - 1) :
    {x : Q | ((upd (qs n) (recSeq qs r0 n) x : Fin (card Q)) : ℕ) ≤
        ((recSeq qs r0 n (qs n) : Fin (card Q)) : ℕ)} = ↑(infSetF qs) := by
  classical
  set r := recSeq qs r0 n with hr
  set q := qs n with hq
  set m := (infSetF qs).card with hm
  have hmpos : 0 < m := Finset.card_pos.2 (infSetF_nonempty qs)
  ext x
  simp only [Set.mem_setOf_eq, Finset.mem_coe]
  constructor
  · intro hx
    by_cases hxq : x = q
    · rw [hxq]; exact hread
    · have hge : ((r x : Fin (card Q)) : ℕ) ≤ ((upd q r x : Fin (card Q)) : ℕ) := by
        by_cases hlt : ((r x : Fin (card Q)) : ℕ) < ((r q : Fin (card Q)) : ℕ)
        · rw [upd_of_ne_lt hxq hlt]; omega
        · rw [upd_of_ne_not_lt hxq hlt]
      refine (hrank x).1 ?_
      omega
  · intro hx
    have hlt : ((r x : Fin (card Q)) : ℕ) < m := (hrank x).2 hx
    by_cases hxq : x = q
    · rw [hxq]
      simp [upd_self]
    · by_cases hcase : ((r x : Fin (card Q)) : ℕ) < ((r q : Fin (card Q)) : ℕ)
      · rw [upd_of_ne_lt hxq hcase]
        omega
      · rw [upd_of_ne_not_lt hxq hcase]
        omega

/-- The largest rank among the states occurring infinitely often is read infinitely
often. -/
theorem infinitely_often_max_rank (hr0 : Function.Injective r0) (N : ℕ)
    (hgood : (∀ n, N ≤ n → ∀ x : Q,
        (((recSeq qs r0 n x : Fin (card Q)) : ℕ) < (infSetF qs).card ↔ x ∈ infSetF qs))) :
    ∀ M : ℕ, ∃ n, M ≤ n ∧
      ((recSeq qs r0 n (qs n) : Fin (card Q)) : ℕ) = (infSetF qs).card - 1 := by
  classical
  intro M
  set m := (infSetF qs).card with hm
  have hmpos : 0 < m := Finset.card_pos.2 (infSetF_nonempty qs)
  set K := max M N with hK
  -- some state occurring infinitely often has the largest rank at time `K`
  have hK' : ∀ x : Q, (((rank (shiftSeq qs) r0 K x : Fin (card Q)) : ℕ) <
      (infSetF (shiftSeq qs)).card ↔ x ∈ infSetF (shiftSeq qs)) := by
    intro x
    rw [infSetF_shift, ← recSeq_eq_rank]
    exact hgood K (le_max_right _ _) x
  obtain ⟨x, hxR, hxrank⟩ := exists_rank_eq (shiftSeq qs) r0 hr0 hK'
    (v := m - 1) (by rw [infSetF_shift]; omega)
  rw [infSetF_shift] at hxR
  -- `x` is read again after time `K`
  have hinf : {j | shiftSeq qs j = x}.Infinite := by
    rw [infinite_shift_iff]
    exact (mem_infSetF qs).1 hxR
  have hex : ∃ j, K < j ∧ shiftSeq qs j = x := by
    obtain ⟨j, hj, hgt⟩ := hinf.exists_gt K
    exact ⟨j, hgt, hj⟩
  classical
  set j := Nat.find hex with hj
  obtain ⟨hjgt, hjx⟩ : K < j ∧ shiftSeq qs j = x := Nat.find_spec hex
  have hjmin : ∀ i, K < i → i < j → shiftSeq qs i ≠ x := by
    intro i hi1 hi2 hcon
    exact (Nat.find_min hex hi2) ⟨hi1, hcon⟩
  -- the rank of `x` does not change between `K` and `j - 1`
  have hmono : ((rank (shiftSeq qs) r0 K x : Fin (card Q)) : ℕ) ≤
      ((rank (shiftSeq qs) r0 (j - 1) x : Fin (card Q)) : ℕ) :=
    rank_mono_of_untouched (shiftSeq qs) r0 (by omega)
      (fun i hi1 hi2 => hjmin i hi1 (by omega))
  have hlt : ((rank (shiftSeq qs) r0 (j - 1) x : Fin (card Q)) : ℕ) < m := by
    have := hgood (j - 1) (by omega) x
    rw [← recSeq_eq_rank]
    exact this.2 hxR
  refine ⟨j - 1, by omega, ?_⟩
  have hread : qs (j - 1) = x := by
    have : shiftSeq qs j = qs (j - 1) := rfl
    rw [← this]
    exact hjx
  rw [hread, recSeq_eq_rank]
  omega

end Main

/-! ### Correctness of the translation -/

theorem exists_even_maxInfOften_iff (acc : Set (Set Q)) [DecidablePred (· ∈ acc)] (qs : ℕ → Q)
    {r0 : Q → Fin (card Q)} (hr0 : Function.Injective r0) :
    (∃ p, MaxInfOften (fun n => prioOf acc (qs n) (recSeq qs r0 n)) p ∧ Even p)
      ↔ {q : Q | {n | qs n = q}.Infinite} ∈ acc := by
  classical
  set m := (infSetF qs).card with hm
  have hmpos : 0 < m := Finset.card_pos.2 (infSetF_nonempty qs)
  obtain ⟨N, hgood, hread⟩ := exists_good_time qs hr0
  have hcoe : ({q : Q | {n | qs n = q}.Infinite} : Set Q) = ↑(infSetF qs) := (coe_infSetF qs).symm
  -- the rank of the state that is read is at most `m - 1` from time `N` on
  have hle : ∀ n, N ≤ n → ((recSeq qs r0 n (qs n) : Fin (card Q)) : ℕ) ≤ m - 1 := by
    intro n hn
    have := (hgood n hn (qs n)).2 (hread n hn)
    omega
  -- the priority at a time of maximal rank
  have hmaxprio : ∀ n, N ≤ n → ((recSeq qs r0 n (qs n) : Fin (card Q)) : ℕ) = m - 1 →
      prioOf acc (qs n) (recSeq qs r0 n)
        = if (↑(infSetF qs) : Set Q) ∈ acc then 2 * (m - 1) + 2 else 2 * (m - 1) + 1 := by
    intro n hn hrk
    have hset := recent_set_eq (hgood n hn) (hread n hn) hrk
    rw [prioOf, hset, hrk]
  have hinfmax := infinitely_often_max_rank hr0 N hgood
  by_cases hacc : (↑(infSetF qs) : Set Q) ∈ acc
  · -- the maximal priority occurring infinitely often is `2 * (m - 1) + 2`
    refine ⟨fun _ => by rw [hcoe]; exact hacc, fun _ => ?_⟩
    refine ⟨2 * (m - 1) + 2, ⟨fun M => ?_, fun j hj hjinf => ?_⟩, ⟨m - 1 + 1, by ring⟩⟩
    · obtain ⟨n, hn, hrk⟩ := hinfmax (max M N)
      refine ⟨n, by omega, ?_⟩
      show prioOf acc (qs n) (recSeq qs r0 n) = 2 * (m - 1) + 2
      rw [hmaxprio n (by omega) hrk, if_pos hacc]
    · obtain ⟨n, hn, hval⟩ := hjinf N
      have hval' : prioOf acc (qs n) (recSeq qs r0 n) = j := hval
      have hbd : prioOf acc (qs n) (recSeq qs r0 n) ≤ 2 * (m - 1) + 2 := by
        rw [prioOf]
        have := hle n hn
        split <;> omega
      omega
  · -- the maximal priority occurring infinitely often is `2 * (m - 1) + 1`, which is odd
    have hmax1 : MaxInfOften (fun n => prioOf acc (qs n) (recSeq qs r0 n)) (2 * (m - 1) + 1) := by
      refine ⟨fun M => ?_, fun j hj hjinf => ?_⟩
      · obtain ⟨n, hn, hrk⟩ := hinfmax (max M N)
        refine ⟨n, by omega, ?_⟩
        show prioOf acc (qs n) (recSeq qs r0 n) = 2 * (m - 1) + 1
        rw [hmaxprio n (by omega) hrk, if_neg hacc]
      · obtain ⟨n, hn, hval⟩ := hjinf N
        have hval' : prioOf acc (qs n) (recSeq qs r0 n) = j := hval
        have hbd : prioOf acc (qs n) (recSeq qs r0 n) ≤ 2 * (m - 1) + 1 := by
          by_cases hrk : ((recSeq qs r0 n (qs n) : Fin (card Q)) : ℕ) = m - 1
          · rw [hmaxprio n hn hrk, if_neg hacc]
          · have hlt : ((recSeq qs r0 n (qs n) : Fin (card Q)) : ℕ) < m - 1 := by
              have := hle n hn
              omega
            rw [prioOf]
            split <;> omega
        omega
    constructor
    · rintro ⟨p, hp, hpe⟩
      exact absurd (hp.unique hmax1 ▸ hpe) (by simp [parity_simps])
    · intro hc
      rw [hcoe] at hc
      exact absurd hc hacc

end LARSeq

end Lax369799Proofs.WordAutomata
