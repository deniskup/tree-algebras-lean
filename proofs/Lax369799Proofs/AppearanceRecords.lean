/-
Adapted from the Lean ancillary files of Bojańczyk, Casares, Manthe and
Parys, arXiv:2611.10136v1 (2026), with incorporation authorized by the user.
Original module: BorelMSO.Basic.LAR.
Changes: Archive module paths and namespaces; port to the pinned toolchain.
See external-proofs.json for source provenance.
-/
import Mathlib.Data.Finset.Max
import Mathlib.Data.Set.Finite.Lattice
import Mathlib.Order.Interval.Finset.Nat

/-!
# Latest appearance records

This file develops the *latest appearance record* (LAR) of a sequence of states, which is
the classical device used to translate a Muller condition into a condition on priorities.

The record is represented by a *rank function* `r : Q → Fin N` (`N = |Q|`), where `r x` is
the number of states that were seen more recently than `x`; thus the most recently seen
state has rank `0`.  Reading a state `q` updates the record by `LAR.upd q`.

The main result is `LAR.eventually_rank_lt_card`: after a finite time, the states of rank
smaller than `|R|` are exactly the states `R` occurring infinitely often in the sequence.
This is what makes the pair (rank of the state that is read, set of states of smaller or
equal rank) an adequate priority: see `Lax369799Proofs.WordAutomata/Basic/ConjEquiv.lean`.
-/

namespace Lax369799Proofs.WordAutomata

namespace LAR

variable {Q : Type} [Fintype Q] [DecidableEq Q] [Nonempty Q]

/-- The number of states. -/
abbrev card (Q : Type) [Fintype Q] : ℕ := Fintype.card Q

omit [DecidableEq Q] in
theorem card_pos : 0 < card Q := Fintype.card_pos

/-- Reading the state `q` updates the ranks: `q` gets rank `0`, the states that had a
smaller rank than `q` are pushed back by one, the others are unchanged. -/
def upd (q : Q) (r : Q → Fin (card Q)) : Q → Fin (card Q) := fun x =>
  if x = q then ⟨0, card_pos⟩
  else if h : (r x : ℕ) < (r q : ℕ) then ⟨(r x : ℕ) + 1, by omega⟩
  else r x

@[simp] theorem upd_self (q : Q) (r : Q → Fin (card Q)) : (upd q r q : ℕ) = 0 := by
  simp [upd]

theorem upd_of_ne_lt {q x : Q} {r : Q → Fin (card Q)} (hx : x ≠ q) (h : (r x : ℕ) < (r q : ℕ)) :
    ((upd q r x : Fin (card Q)) : ℕ) = (r x : ℕ) + 1 := by
  simp [upd, hx, h]

theorem upd_of_ne_not_lt {q x : Q} {r : Q → Fin (card Q)} (hx : x ≠ q)
    (h : ¬ (r x : ℕ) < (r q : ℕ)) : ((upd q r x : Fin (card Q)) : ℕ) = (r x : ℕ) := by
  simp [upd, hx, h]

/-- The update preserves injectivity of the rank function. -/
theorem upd_injective {q : Q} {r : Q → Fin (card Q)} (hr : Function.Injective r) :
    Function.Injective (upd q r) := by
  intro x y hxy
  by_cases hx : x = q
  · by_cases hy : y = q
    · rw [hx, hy]
    · exfalso
      have h1 : ((upd q r x : Fin (card Q)) : ℕ) = 0 := by rw [hx]; simp
      have h2 : ((upd q r y : Fin (card Q)) : ℕ) ≠ 0 := by
        by_cases h : (r y : ℕ) < (r q : ℕ)
        · rw [upd_of_ne_lt hy h]; omega
        · rw [upd_of_ne_not_lt hy h]
          intro h0
          apply hy
          apply hr
          have : (r q : ℕ) = 0 := by omega
          exact Fin.ext (by omega)
      rw [hxy] at h1
      exact h2 h1
  · by_cases hy : y = q
    · exfalso
      have h1 : ((upd q r y : Fin (card Q)) : ℕ) = 0 := by rw [hy]; simp
      have h2 : ((upd q r x : Fin (card Q)) : ℕ) ≠ 0 := by
        by_cases h : (r x : ℕ) < (r q : ℕ)
        · rw [upd_of_ne_lt hx h]; omega
        · rw [upd_of_ne_not_lt hx h]
          intro h0
          apply hx
          apply hr
          have : (r q : ℕ) = 0 := by omega
          exact Fin.ext (by omega)
      rw [hxy] at h2
      exact h2 h1
    · apply hr
      have hxv := congrArg (fun z : Fin (card Q) => (z : ℕ)) hxy
      have hxq : (r x : ℕ) ≠ (r q : ℕ) := fun h => hx (hr (Fin.ext h))
      have hyq : (r y : ℕ) ≠ (r q : ℕ) := fun h => hy (hr (Fin.ext h))
      by_cases h1 : (r x : ℕ) < (r q : ℕ) <;> by_cases h2 : (r y : ℕ) < (r q : ℕ)
      · rw [upd_of_ne_lt hx h1, upd_of_ne_lt hy h2] at hxv
        exact Fin.ext (by omega)
      · rw [upd_of_ne_lt hx h1, upd_of_ne_not_lt hy h2] at hxv
        exact absurd hxv (by omega)
      · rw [upd_of_ne_not_lt hx h1, upd_of_ne_lt hy h2] at hxv
        exact absurd hxv (by omega)
      · rw [upd_of_ne_not_lt hx h1, upd_of_ne_not_lt hy h2] at hxv
        exact Fin.ext hxv

/-- The rank of a state that is not read does not decrease. -/
theorem le_upd {q x : Q} (hx : x ≠ q) (r : Q → Fin (card Q)) :
    (r x : ℕ) ≤ ((upd q r x : Fin (card Q)) : ℕ) := by
  by_cases h : (r x : ℕ) < (r q : ℕ)
  · rw [upd_of_ne_lt hx h]; omega
  · rw [upd_of_ne_not_lt hx h]

/-- Every state other than the one that is read gets a positive rank. -/
theorem upd_pos {q x : Q} (hx : x ≠ q) {r : Q → Fin (card Q)} (hr : Function.Injective r) :
    0 < ((upd q r x : Fin (card Q)) : ℕ) := by
  by_cases h : (r x : ℕ) < (r q : ℕ)
  · rw [upd_of_ne_lt hx h]; omega
  · rw [upd_of_ne_not_lt hx h]
    rcases Nat.eq_zero_or_pos (r x : ℕ) with h0 | h0
    · exfalso
      apply hx
      apply hr
      exact Fin.ext (by omega)
    · exact h0

/-- The update preserves the relative order of the states that are not read. -/
theorem upd_lt_of_lt {q x y : Q} (hx : x ≠ q) (hy : y ≠ q) {r : Q → Fin (card Q)}
    (hr : Function.Injective r) (h : (r x : ℕ) < (r y : ℕ)) :
    ((upd q r x : Fin (card Q)) : ℕ) < ((upd q r y : Fin (card Q)) : ℕ) := by
  have hyq : (r y : ℕ) ≠ (r q : ℕ) := fun hh => hy (hr (Fin.ext hh))
  by_cases h1 : (r x : ℕ) < (r q : ℕ) <;> by_cases h2 : (r y : ℕ) < (r q : ℕ)
  · rw [upd_of_ne_lt hx h1, upd_of_ne_lt hy h2]; omega
  · rw [upd_of_ne_lt hx h1, upd_of_ne_not_lt hy h2]; omega
  · rw [upd_of_ne_not_lt hx h1, upd_of_ne_lt hy h2]; omega
  · rw [upd_of_ne_not_lt hx h1, upd_of_ne_not_lt hy h2]; omega


/-! ### The record along a sequence of states -/

variable (qs : ℕ → Q) (r0 : Q → Fin (card Q))

/-- The rank function after reading the first `n` states of the sequence `qs` (the state
`qs 0` is the initial one and is not read). -/
def rank : ℕ → (Q → Fin (card Q))
  | 0 => r0
  | n + 1 => upd (qs (n + 1)) (rank n)

@[simp] theorem rank_zero : rank qs r0 0 = r0 := rfl

@[simp] theorem rank_succ (n : ℕ) : rank qs r0 (n + 1) = upd (qs (n + 1)) (rank qs r0 n) := rfl

theorem rank_injective (hr0 : Function.Injective r0) : ∀ n, Function.Injective (rank qs r0 n)
  | 0 => hr0
  | n + 1 => upd_injective (rank_injective hr0 n)

theorem rank_touch (n : ℕ) : ((rank qs r0 (n + 1) (qs (n + 1)) : Fin (card Q)) : ℕ) = 0 :=
  upd_self _ _

/-- The rank of a state that is not read in `(a, b]` does not decrease. -/
theorem rank_mono_of_untouched {x : Q} {a b : ℕ} (hab : a ≤ b)
    (h : ∀ j, a < j → j ≤ b → qs j ≠ x) :
    ((rank qs r0 a x : Fin (card Q)) : ℕ) ≤ ((rank qs r0 b x : Fin (card Q)) : ℕ) := by
  induction b, hab using Nat.le_induction with
  | base => exact le_rfl
  | succ b hab ih =>
    refine le_trans (ih (fun j hj1 hj2 => h j hj1 (by omega))) ?_
    rw [rank_succ]
    exact le_upd (fun hcon => h (b + 1) (by omega) le_rfl (by rw [hcon])) _

/-- The update preserves the relative order of two states that are not read. -/
theorem rank_lt_of_untouched (hr0 : Function.Injective r0) {x y : Q} {a b : ℕ} (hab : a ≤ b)
    (hx : ∀ j, a < j → j ≤ b → qs j ≠ x) (hy : ∀ j, a < j → j ≤ b → qs j ≠ y)
    (h : ((rank qs r0 a x : Fin (card Q)) : ℕ) < ((rank qs r0 a y : Fin (card Q)) : ℕ)) :
    ((rank qs r0 b x : Fin (card Q)) : ℕ) < ((rank qs r0 b y : Fin (card Q)) : ℕ) := by
  induction b, hab using Nat.le_induction with
  | base => exact h
  | succ b hab ih =>
    have ih' := ih (fun j hj1 hj2 => hx j hj1 (by omega)) (fun j hj1 hj2 => hy j hj1 (by omega))
    rw [rank_succ]
    exact upd_lt_of_lt (fun hcon => hx (b + 1) (by omega) le_rfl (by rw [hcon]))
      (fun hcon => hy (b + 1) (by omega) le_rfl (by rw [hcon]))
      (rank_injective qs r0 hr0 b) ih'

/-- The states read in the interval `(a, b]`. -/
def touched (a b : ℕ) : Finset Q := (Finset.Ioc a b).image qs

omit [Fintype Q] [Nonempty Q] in
theorem mem_touched {a b : ℕ} {x : Q} :
    x ∈ touched qs a b ↔ ∃ j, a < j ∧ j ≤ b ∧ qs j = x := by
  simp [touched, Finset.mem_image, Finset.mem_Ioc, and_assoc]

omit [Fintype Q] [Nonempty Q] in
theorem touched_mono {a b b' : ℕ} (h : b ≤ b') : touched qs a b ⊆ touched qs a b' := by
  intro x hx
  rw [mem_touched] at hx ⊢
  obtain ⟨j, hj1, hj2, hj3⟩ := hx
  exact ⟨j, hj1, by omega, hj3⟩

omit [Fintype Q] [Nonempty Q] in
@[simp] theorem touched_self (a : ℕ) : touched qs a a = ∅ := by
  simp [touched]

/-- A state read after the last time `x` was read has a smaller rank than `x`. -/
theorem rank_lt_of_mem_touched (hr0 : Function.Injective r0) {x p : Q} {a b : ℕ}
    (hxp : p ≠ x) (hp : p ∈ touched qs a b) (hx : ∀ j, a < j → j ≤ b → qs j ≠ x) :
    ((rank qs r0 b p : Fin (card Q)) : ℕ) < ((rank qs r0 b x : Fin (card Q)) : ℕ) := by
  classical
  -- take the last time in `(a, b]` at which `p` is read
  set T : Finset ℕ := (Finset.Ioc a b).filter (fun j => qs j = p) with hT
  have hTne : T.Nonempty := by
    rw [mem_touched] at hp
    obtain ⟨j, hj1, hj2, hj3⟩ := hp
    exact ⟨j, by simp [hT, Finset.mem_filter, Finset.mem_Ioc]; exact ⟨⟨hj1, hj2⟩, hj3⟩⟩
  obtain ⟨j, hjT, hjmax⟩ := T.exists_max_image id hTne
  simp only [hT, Finset.mem_filter, Finset.mem_Ioc] at hjT
  obtain ⟨⟨hja, hjb⟩, hjp⟩ := hjT
  -- at time `j` the state `p` has rank `0` and `x` has a positive rank
  obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
  have hp0 : ((rank qs r0 (j' + 1) p : Fin (card Q)) : ℕ) = 0 := by
    rw [← hjp]; exact rank_touch qs r0 j'
  have hxpos : 0 < ((rank qs r0 (j' + 1) x : Fin (card Q)) : ℕ) := by
    rcases Nat.eq_zero_or_pos ((rank qs r0 (j' + 1) x : Fin (card Q)) : ℕ) with h0 | h0
    · exfalso
      apply hxp
      apply rank_injective qs r0 hr0 (j' + 1)
      exact Fin.ext (by omega)
    · exact h0
  -- afterwards neither `p` nor `x` is read
  refine rank_lt_of_untouched qs r0 hr0 hjb ?_ ?_ (by omega)
  · intro i hi1 hi2 hcon
    have : i ∈ T := by
      simp [hT, Finset.mem_filter, Finset.mem_Ioc]
      exact ⟨⟨by omega, hi2⟩, hcon⟩
    have := hjmax i this
    simp only [id] at this
    omega
  · intro i hi1 hi2
    exact hx i (by omega) hi2

/-- **Key bound.**  If `x` is read at time `a` and not read again up to time `b`, then its
rank at time `b` is smaller than the number of distinct states read in `(a, b]`, together
with `x` itself. -/
theorem rank_lt_card_touched (hr0 : Function.Injective r0) {x : Q} {a b : ℕ} (hab : a ≤ b)
    (h0 : ((rank qs r0 a x : Fin (card Q)) : ℕ) = 0)
    (hx : ∀ j, a < j → j ≤ b → qs j ≠ x) :
    ((rank qs r0 b x : Fin (card Q)) : ℕ) < (insert x (touched qs a b)).card := by
  classical
  induction b, hab using Nat.le_induction with
  | base =>
    rw [h0]
    simp
  | succ b hab ih =>
    have hx' : ∀ j, a < j → j ≤ b → qs j ≠ x := fun j hj1 hj2 => hx j hj1 (by omega)
    have ih' := ih hx'
    have hpx : qs (b + 1) ≠ x := hx (b + 1) (by omega) le_rfl
    set p := qs (b + 1) with hp
    have hcardmono : (insert x (touched qs a b)).card ≤ (insert x (touched qs a (b + 1))).card :=
      Finset.card_le_card (Finset.insert_subset_insert _ (touched_mono qs (by omega)))
    by_cases hlt : ((rank qs r0 b x : Fin (card Q)) : ℕ) < ((rank qs r0 b p : Fin (card Q)) : ℕ)
    · -- then `p` has not been read in `(a, b]`
      have hpnew : p ∉ insert x (touched qs a b) := by
        intro hmem
        rcases Finset.mem_insert.1 hmem with h | h
        · exact hpx h
        · exact absurd (rank_lt_of_mem_touched qs r0 hr0 hpx h hx') (by omega)
      have hins : insert x (touched qs a (b + 1)) = insert p (insert x (touched qs a b)) := by
        ext y
        simp only [Finset.mem_insert, mem_touched]
        constructor
        · rintro (rfl | ⟨j, hj1, hj2, rfl⟩)
          · exact Or.inr (Or.inl rfl)
          · rcases Nat.lt_or_ge j (b + 1) with hjb | hjb
            · exact Or.inr (Or.inr ⟨j, hj1, by omega, rfl⟩)
            · exact Or.inl (by rw [show j = b + 1 from by omega])
        · rintro (rfl | rfl | ⟨j, hj1, hj2, rfl⟩)
          · exact Or.inr ⟨b + 1, by omega, le_rfl, rfl⟩
          · exact Or.inl rfl
          · exact Or.inr ⟨j, hj1, by omega, rfl⟩
      rw [hins, Finset.card_insert_of_notMem hpnew]
      have : ((rank qs r0 (b + 1) x : Fin (card Q)) : ℕ)
          = ((rank qs r0 b x : Fin (card Q)) : ℕ) + 1 := by
        rw [rank_succ]
        exact upd_of_ne_lt (Ne.symm hpx) hlt
      omega
    · have : ((rank qs r0 (b + 1) x : Fin (card Q)) : ℕ)
          = ((rank qs r0 b x : Fin (card Q)) : ℕ) := by
        rw [rank_succ]
        exact upd_of_ne_not_lt (Ne.symm hpx) hlt
      omega

/-! ### The states of small rank are exactly those occurring infinitely often -/

open Classical in
/-- The states occurring infinitely often in the sequence. -/
noncomputable def infSetF (qs : ℕ → Q) : Finset Q :=
  Finset.univ.filter (fun x => {n | qs n = x}.Infinite)

omit [DecidableEq Q] [Nonempty Q] in
theorem mem_infSetF {x : Q} : x ∈ infSetF qs ↔ {n | qs n = x}.Infinite := by
  classical
  simp [infSetF]

omit [Nonempty Q] in
/-- After some time, only states occurring infinitely often are read. -/
theorem exists_eventually_mem_infSetF : ∃ N₀ : ℕ, ∀ n, N₀ ≤ n → qs n ∈ infSetF qs := by
  classical
  have hfin : {n : ℕ | qs n ∉ infSetF qs}.Finite := by
    have hsub : {n : ℕ | qs n ∉ infSetF qs}
        ⊆ ⋃ x ∈ {x : Q | x ∉ infSetF qs}, {n | qs n = x} := by
      intro n hn
      exact Set.mem_biUnion hn rfl
    refine Set.Finite.subset (Set.Finite.biUnion (Set.toFinite _) (fun x hx => ?_)) hsub
    exact Set.not_infinite.1 (fun hcon => hx ((mem_infSetF qs).2 hcon))
  obtain ⟨N, hN⟩ := hfin.bddAbove
  refine ⟨N + 1, fun n hn => ?_⟩
  by_contra hcon
  have := hN (show n ∈ {n : ℕ | qs n ∉ infSetF qs} from hcon)
  omega

/-- **Correctness of the latest appearance record.**  From some time on, the states whose
rank is smaller than the number `m` of states occurring infinitely often are exactly those
states.  In particular the state of rank `m - 1` is the "oldest" of them. -/
theorem eventually_rank_lt_card (hr0 : Function.Injective r0) :
    ∃ N₁ : ℕ, ∀ n, N₁ ≤ n → ∀ x : Q,
      (((rank qs r0 n x : Fin (card Q)) : ℕ) < (infSetF qs).card ↔ x ∈ infSetF qs) := by
  classical
  obtain ⟨N₀, hN₀⟩ := exists_eventually_mem_infSetF qs
  have hchoice : ∀ x : Q, ∃ a : ℕ, x ∈ infSetF qs → (N₀ < a ∧ qs a = x) := by
    intro x
    by_cases hx : x ∈ infSetF qs
    · rw [mem_infSetF] at hx
      obtain ⟨a, hamem, hgt⟩ := hx.exists_gt N₀
      exact ⟨a, fun _ => ⟨hgt, hamem⟩⟩
    · exact ⟨0, fun hc => absurd hc hx⟩
  choose a ha using hchoice
  refine ⟨(infSetF qs).sup a, fun n hn x => ?_⟩
  have hinj : Function.Injective (fun y : Q => ((rank qs r0 n y : Fin (card Q)) : ℕ)) := by
    intro u v huv
    exact rank_injective qs r0 hr0 n (Fin.ext huv)
  -- every state occurring infinitely often has rank smaller than their number
  have key : ∀ y ∈ infSetF qs, ((rank qs r0 n y : Fin (card Q)) : ℕ) < (infSetF qs).card := by
    intro y hy
    set T : Finset ℕ := (Finset.Ioc N₀ n).filter (fun j => qs j = y) with hT
    have hTne : T.Nonempty := by
      refine ⟨a y, ?_⟩
      simp only [hT, Finset.mem_filter, Finset.mem_Ioc]
      exact ⟨⟨(ha y hy).1, le_trans (Finset.le_sup hy) hn⟩, (ha y hy).2⟩
    obtain ⟨j, hjT, hjmax⟩ := T.exists_max_image id hTne
    simp only [hT, Finset.mem_filter, Finset.mem_Ioc] at hjT
    obtain ⟨⟨hj0, hjn⟩, hjy⟩ := hjT
    obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
    have h0 : ((rank qs r0 (j' + 1) y : Fin (card Q)) : ℕ) = 0 := by
      rw [← hjy]; exact rank_touch qs r0 j'
    have huntouched : ∀ i, j' + 1 < i → i ≤ n → qs i ≠ y := by
      intro i hi1 hi2 hcon
      have hiT : i ∈ T := by
        simp only [hT, Finset.mem_filter, Finset.mem_Ioc]
        exact ⟨⟨by omega, hi2⟩, hcon⟩
      have := hjmax i hiT
      simp only [id] at this
      omega
    have hbound := rank_lt_card_touched qs r0 hr0 (show j' + 1 ≤ n by omega) h0 huntouched
    have hsub : insert y (touched qs (j' + 1) n) ⊆ infSetF qs := by
      intro z hz
      rcases Finset.mem_insert.1 hz with rfl | hz
      · exact hy
      · rw [mem_touched] at hz
        obtain ⟨i, hi1, hi2, rfl⟩ := hz
        exact hN₀ i (by omega)
    exact lt_of_lt_of_le hbound (Finset.card_le_card hsub)
  refine ⟨fun hlt => ?_, key x⟩
  by_contra hxR
  have himg : (infSetF qs).image (fun y : Q => ((rank qs r0 n y : Fin (card Q)) : ℕ))
      = Finset.range (infSetF qs).card := by
    refine Finset.eq_of_subset_of_card_le ?_ ?_
    · intro v hv
      simp only [Finset.mem_image] at hv
      obtain ⟨y, hy, rfl⟩ := hv
      exact Finset.mem_range.2 (key y hy)
    · rw [Finset.card_range, Finset.card_image_of_injective _ hinj]
  have hmem : ((rank qs r0 n x : Fin (card Q)) : ℕ) ∈ Finset.range (infSetF qs).card :=
    Finset.mem_range.2 hlt
  rw [← himg] at hmem
  simp only [Finset.mem_image] at hmem
  obtain ⟨y, hy, hyx⟩ := hmem
  exact hxR (hinj hyx ▸ hy)

omit [DecidableEq Q] [Nonempty Q] in
/-- Some state occurs infinitely often. -/
theorem infSetF_nonempty : (infSetF qs).Nonempty := by
  classical
  rw [Finset.nonempty_iff_ne_empty]
  intro hempty
  have hfin : ∀ x : Q, {n | qs n = x}.Finite := by
    intro x
    refine Set.not_infinite.1 (fun hcon => ?_)
    have : x ∈ infSetF qs := (mem_infSetF qs).2 hcon
    rw [hempty] at this
    exact absurd this (Finset.notMem_empty x)
  have hsub : (Set.univ : Set ℕ) ⊆ ⋃ x : Q, {n | qs n = x} := fun n _ => Set.mem_iUnion.2 ⟨qs n, rfl⟩
  exact Set.infinite_univ (Set.Finite.subset (Set.finite_iUnion hfin) hsub)

/-- Once the states of rank `< m` are exactly those occurring infinitely often, all the
ranks below `m` are attained by such states. -/
theorem exists_rank_eq (hr0 : Function.Injective r0) {n : ℕ}
    (hn : ∀ x : Q, (((rank qs r0 n x : Fin (card Q)) : ℕ) < (infSetF qs).card ↔ x ∈ infSetF qs))
    {v : ℕ} (hv : v < (infSetF qs).card) :
    ∃ x, x ∈ infSetF qs ∧ ((rank qs r0 n x : Fin (card Q)) : ℕ) = v := by
  classical
  have hinj : Function.Injective (fun y : Q => ((rank qs r0 n y : Fin (card Q)) : ℕ)) :=
    fun u v h => rank_injective qs r0 hr0 n (Fin.ext h)
  have himg : (infSetF qs).image (fun y : Q => ((rank qs r0 n y : Fin (card Q)) : ℕ))
      = Finset.range (infSetF qs).card := by
    refine Finset.eq_of_subset_of_card_le ?_ ?_
    · intro w hw
      simp only [Finset.mem_image] at hw
      obtain ⟨y, hy, rfl⟩ := hw
      exact Finset.mem_range.2 ((hn y).2 hy)
    · rw [Finset.card_range, Finset.card_image_of_injective _ hinj]
  have hv' : v ∈ (infSetF qs).image (fun y : Q => ((rank qs r0 n y : Fin (card Q)) : ℕ)) := by
    rw [himg]
    exact Finset.mem_range.2 hv
  simpa only [Finset.mem_image] using hv'

end LAR

end Lax369799Proofs.WordAutomata
