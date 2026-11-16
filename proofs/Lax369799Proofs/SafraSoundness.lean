/-
Adapted from the Lean ancillary files of Bojańczyk, Casares, Manthe and
Parys, arXiv:2611.10136v1 (2026), with incorporation authorized by the user.
Original module: BorelMSO.Safra.Sound.
Changes: Archive module paths and namespaces; port to the pinned toolchain.
See external-proofs.json for source provenance.
-/
import Lax369799Proofs.SafraRuns
import Lax369799Proofs.WordCompactness
import Mathlib.Data.Finset.Max
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Algebra.Order.Interval.Finset.SuccPred

/-!
# Safra's construction: soundness

This file proves one half of the correctness of Safra's construction: if along the run of
the construction on an ω-word `w` some node `p` is present from some time on and is marked
infinitely often, then the Büchi automaton accepts `w`
(`Lax369799Proofs.WordAutomata.Safra.accepts_of_node`).

The argument is the classical one.  Between two consecutive markings of `p`, every state of
the label of `p` is reached from a state of the label of `p` at the previous marking by a
partial run visiting the Büchi set: indeed at a marking the label of `p` is covered by the
labels of its children, and the children present at that moment have been created after the
previous marking (at which all of them were deleted), so that the states they contain have
gone through the Büchi set.  A Kőnig argument then produces an infinite run visiting the
Büchi set infinitely often.
-/

namespace Lax369799Proofs.WordAutomata

namespace Safra

open scoped Classical

variable {Q Gam : Type} [Fintype Q] {B : NBuchi Q Gam} {w : ℕ → Gam}

/-- The label of the node `p` at time `n`. -/
def labAt (B : NBuchi Q Gam) (w : ℕ → Gam) (p : Pos Q) (n : ℕ) : Set Q :=
  (treeRun B w n).lab p

/-- The union of the labels of the children of `p` at time `n`. -/
def childUnion (B : NBuchi Q Gam) (w : ℕ → Gam) (p : Pos Q) (n : ℕ) : Set Q :=
  ⋃ i : Slot Q, (treeRun B w n).lab (i :: p)

/-! ### One step -/

/-- Every state of the label of `p` at time `n + 1` comes from a state of the label of `p`
at time `n`. -/
theorem mem_labAt_succ {p : Pos Q} {n : ℕ} (hne : labAt B w p n ≠ ∅) {q : Q}
    (hq : q ∈ labAt B w p (n + 1)) :
    ∃ q0 ∈ labAt B w p n, B.step q0 (w n) q := by
  have h1 : q ∈ lab1 B (treeRun B w n) (w n) p :=
    lab2_subset_lab1 B _ _ p (stepTree_lab_subset B _ _ p hq)
  match p with
  | [] => exact mem_lab1_nil B _ _ h1
  | i :: p' =>
      rw [lab1_cons_of_lab_ne B _ _ hne] at h1
      obtain ⟨q0, hq0, hstep⟩ := h1
      exact ⟨q0, hq0, hstep⟩

/-- Every state of `lab2` of a child of `p` comes from a state of the label of `p`, and it
comes from a child of `p` unless the state it comes from is in the Büchi set. -/
theorem mem_lab2_child {p : Pos Q} {i : Slot Q} {n : ℕ} {q : Q}
    (hq : q ∈ lab2 B (treeRun B w n) (w n) (i :: p)) :
    ∃ q0 ∈ labAt B w p n, B.step q0 (w n) q ∧ (q0 ∈ B.fin ∨ q0 ∈ childUnion B w p n) := by
  have h1 : q ∈ lab1 B (treeRun B w n) (w n) (i :: p) := lab2_subset_lab1 B _ _ _ hq
  obtain ⟨q0, hq0, hstep, hcase⟩ :=
    mem_lab1_cons B (treeRun B w n) (w n) h1 ((inv_treeRun B w n).mono i p)
  refine ⟨q0, hq0, hstep, ?_⟩
  rcases hcase with h | h
  · exact Or.inl h
  · exact Or.inr (Set.mem_iUnion.2 ⟨i, h⟩)

/-- Every state of the union of the labels of the children of `p` at time `n + 1` comes from
a state of the label of `p` at time `n`, through the Büchi set or through a child. -/
theorem mem_childUnion_succ {p : Pos Q} {n : ℕ} {q : Q}
    (hq : q ∈ childUnion B w p (n + 1)) :
    ∃ q0 ∈ labAt B w p n, B.step q0 (w n) q ∧ (q0 ∈ B.fin ∨ q0 ∈ childUnion B w p n) := by
  obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hq
  exact mem_lab2_child (stepTree_lab_subset B _ _ _ hi)

/-- At a marking time, the label of `p` is covered by the (pre-deletion) labels of its
children. -/
theorem mem_labAt_of_mark {p : Pos Q} {n : ℕ} (hmark : (treeRun B w (n + 1)).mark p) {q : Q}
    (hq : q ∈ labAt B w p (n + 1)) :
    ∃ q0 ∈ labAt B w p n, B.step q0 (w n) q ∧ (q0 ∈ B.fin ∨ q0 ∈ childUnion B w p n) := by
  obtain ⟨hvm, -⟩ := hmark
  have h2 : q ∈ lab2 B (treeRun B w n) (w n) p := stepTree_lab_subset B _ _ p hq
  obtain ⟨i, hi⟩ := Set.mem_iUnion.1 (hvm.2 h2)
  exact mem_lab2_child hi

/-- At a marking time, all the children of `p` have been deleted. -/
theorem childUnion_eq_empty_of_mark {p : Pos Q} {n : ℕ}
    (hmark : (treeRun B w (n + 1)).mark p) : childUnion B w p (n + 1) = ∅ := by
  obtain ⟨hvm, -⟩ := hmark
  refine Set.eq_empty_of_subset_empty ?_
  intro q hq
  obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hq
  rw [treeRun_succ, stepTree_lab,
    if_pos (killed_cons_of_vmark B (treeRun B w n) (w n) i p hvm)] at hi
  exact hi

/-! ### Counting markings and visits of the Büchi set -/

/-- The number of times the node `p` has been marked in `(t₀, n]`. -/
noncomputable def markCount (B : NBuchi Q Gam) (w : ℕ → Gam) (p : Pos Q) (t0 n : ℕ) : ℕ :=
  ((Finset.Ioc t0 n).filter (fun s => (treeRun B w s).mark p)).card

/-- The number of times `f` visits the Büchi set in `[s, t)`. -/
noncomputable def finCount (B : NBuchi Q Gam) (f : ℕ → Q) (s t : ℕ) : ℕ :=
  ((Finset.Ico s t).filter (fun k => f k ∈ B.fin)).card

@[simp] theorem markCount_self (B : NBuchi Q Gam) (w : ℕ → Gam) (p : Pos Q) (t0 : ℕ) :
    markCount B w p t0 t0 = 0 := by simp [markCount]

theorem markCount_succ (B : NBuchi Q Gam) (w : ℕ → Gam) (p : Pos Q) {t0 n : ℕ}
    (h : t0 ≤ n) : markCount B w p t0 (n + 1) =
      markCount B w p t0 n + (if (treeRun B w (n + 1)).mark p then 1 else 0) := by
  unfold markCount
  rw [← Finset.insert_Ioc_right_eq_Ioc_add_one h, Finset.filter_insert]
  split
  · rw [Finset.card_insert_of_notMem (by simp)]
  · simp

omit [Fintype Q] in
@[simp] theorem finCount_self (B : NBuchi Q Gam) (f : ℕ → Q) (s : ℕ) :
    finCount B f s s = 0 := by simp [finCount]

omit [Fintype Q] in
theorem finCount_succ (B : NBuchi Q Gam) (f : ℕ → Q) {s t : ℕ} (h : s ≤ t) :
    finCount B f s (t + 1) = finCount B f s t + (if f t ∈ B.fin then 1 else 0) := by
  unfold finCount
  rw [Nat.Ico_succ_right_eq_insert_Ico h, Finset.filter_insert]
  split
  · rw [Finset.card_insert_of_notMem (by simp)]
  · simp

omit [Fintype Q] in
theorem finCount_le (B : NBuchi Q Gam) (f : ℕ → Q) (s t : ℕ) : finCount B f s t ≤ t := by
  refine le_trans (Finset.card_filter_le _ _) ?_
  simp [Nat.card_Ico]

omit [Fintype Q] in
theorem finCount_congr (B : NBuchi Q Gam) {f g : ℕ → Q} {s t : ℕ}
    (h : ∀ k, s ≤ k → k < t → f k = g k) : finCount B f s t = finCount B g s t := by
  unfold finCount
  congr 1
  refine Finset.filter_congr ?_
  intro k hk
  simp only [Finset.mem_Ico] at hk
  rw [h k hk.1 hk.2]

/-! ### The witnesses -/

variable (B w)

/-- A partial run from the label of `p` at time `t₀` which, at every intermediate time, has
visited the Büchi set at least as often as `p` has been marked. -/
def GoodRun (p : Pos Q) (t0 n : ℕ) (f : ℕ → Q) : Prop :=
  f t0 ∈ labAt B w p t0 ∧ PRun B w t0 n f ∧
    ∀ m, t0 ≤ m → m ≤ n → markCount B w p t0 m ≤ finCount B f t0 m

variable {B w}

theorem GoodRun.mono {p : Pos Q} {t0 n n' : ℕ} {f : ℕ → Q} (h : GoodRun B w p t0 n f)
    (hn : n' ≤ n) : GoodRun B w p t0 n' f :=
  ⟨h.1, h.2.1.mono (le_refl _) hn, fun m hm hmn => h.2.2 m hm (hmn.trans hn)⟩

/-- Extending a good partial run by one step. -/
theorem good_extend {p : Pos Q} {t0 n : ℕ} (hn : t0 ≤ n) {f : ℕ → Q}
    (hf : GoodRun B w p t0 n f) {q : Q} (hstep : B.step (f n) (w n) q)
    (hcount : markCount B w p t0 (n + 1) ≤
      finCount B f t0 n + (if f n ∈ B.fin then 1 else 0)) :
    ∃ g, GoodRun B w p t0 (n + 1) g ∧ g (n + 1) = q ∧
      finCount B g t0 (n + 1) = finCount B f t0 n + (if f n ∈ B.fin then 1 else 0) := by
  obtain ⟨g, hgf, hgn, hgrun⟩ := exists_prun_succ hf.2.1 hstep
  have hcong : ∀ m, m ≤ n → finCount B g t0 m = finCount B f t0 m := by
    intro m hm
    exact finCount_congr B (fun k _ hk => hgf k (by omega))
  have hkey : finCount B g t0 (n + 1) = finCount B f t0 n + (if f n ∈ B.fin then 1 else 0) := by
    rw [finCount_succ B g hn, hcong n (le_refl n), hgf n (le_refl n)]
  refine ⟨g, ⟨?_, hgrun, ?_⟩, hgn, hkey⟩
  · rw [hgf t0 hn]
    exact hf.1
  · intro m hm hmn
    rcases Nat.lt_or_ge m (n + 1) with hlt | hge
    · rw [hcong m (by omega)]
      exact hf.2.2 m hm (by omega)
    · have : m = n + 1 := by omega
      subst this
      rw [hkey]
      exact hcount

/-- **The key step of the soundness proof.**  If the node `p` is present from the time `t₀`
on and has no child at time `t₀`, then every state of its label at a time `n` is reached by
a partial run which has visited the Büchi set at least as often as `p` has been marked;
moreover the states in the children of `p` have visited it strictly more often. -/
theorem exists_goodRun {p : Pos Q} {t0 : ℕ}
    (halive : ∀ n, t0 ≤ n → labAt B w p n ≠ ∅) (hchild0 : childUnion B w p t0 = ∅) :
    ∀ n, t0 ≤ n →
      (∀ q ∈ labAt B w p n, ∃ f, GoodRun B w p t0 n f ∧ f n = q) ∧
      (∀ q ∈ childUnion B w p n, ∃ f, GoodRun B w p t0 n f ∧ f n = q ∧
        markCount B w p t0 n < finCount B f t0 n) := by
  intro n hn
  induction n, hn using Nat.le_induction with
  | base =>
      refine ⟨fun q hq => ⟨fun _ => q, ⟨hq, fun k hk hk' => by omega, ?_⟩, rfl⟩, ?_⟩
      · intro m hm hmn
        have : m = t0 := by omega
        subst this
        simp
      · intro q hq
        rw [hchild0] at hq
        exact absurd hq (by simp)
  | succ n hn ih =>
      obtain ⟨ih1, ih2⟩ := ih
      -- from a predecessor of `q` we build a good run ending at `q`
      have key : ∀ q0 ∈ labAt B w p n, ∀ q : Q, B.step q0 (w n) q →
          (q0 ∈ B.fin ∨ q0 ∈ childUnion B w p n) →
          ∃ f, GoodRun B w p t0 n f ∧ f n = q0 ∧
            markCount B w p t0 n + 1 ≤ finCount B f t0 n + (if f n ∈ B.fin then 1 else 0) := by
        rintro q0 hq0 q hstep (hfin | hchild)
        · obtain ⟨f, hf, hfn⟩ := ih1 q0 hq0
          refine ⟨f, hf, hfn, ?_⟩
          rw [hfn, if_pos hfin]
          have := hf.2.2 n (by omega) (le_refl n)
          omega
        · obtain ⟨f, hf, hfn, hlt⟩ := ih2 q0 hchild
          exact ⟨f, hf, hfn, by omega⟩
      constructor
      · intro q hq
        by_cases hmark : (treeRun B w (n + 1)).mark p
        · obtain ⟨q0, hq0, hstep, hcase⟩ := mem_labAt_of_mark hmark hq
          obtain ⟨f, hf, hfn, hcount⟩ := key q0 hq0 q hstep hcase
          have hc : markCount B w p t0 (n + 1) ≤
              finCount B f t0 n + (if f n ∈ B.fin then 1 else 0) := by
            rw [markCount_succ B w p hn, if_pos hmark]
            exact hcount
          obtain ⟨g, hg, hgn, -⟩ := good_extend hn hf (by rw [hfn]; exact hstep) hc
          exact ⟨g, hg, hgn⟩
        · obtain ⟨q0, hq0, hstep⟩ := mem_labAt_succ (halive n hn) hq
          obtain ⟨f, hf, hfn⟩ := ih1 q0 hq0
          have hc : markCount B w p t0 (n + 1) ≤
              finCount B f t0 n + (if f n ∈ B.fin then 1 else 0) := by
            rw [markCount_succ B w p hn, if_neg hmark]
            have := hf.2.2 n (by omega) (le_refl n)
            omega
          obtain ⟨g, hg, hgn, -⟩ := good_extend hn hf (by rw [hfn]; exact hstep) hc
          exact ⟨g, hg, hgn⟩
      · intro q hq
        have hmark : ¬ (treeRun B w (n + 1)).mark p := by
          intro hm
          rw [childUnion_eq_empty_of_mark hm] at hq
          exact hq
        have hmc : markCount B w p t0 (n + 1) = markCount B w p t0 n := by
          rw [markCount_succ B w p hn, if_neg hmark, Nat.add_zero]
        obtain ⟨q0, hq0, hstep, hcase⟩ := mem_childUnion_succ hq
        obtain ⟨f, hf, hfn, hcount⟩ := key q0 hq0 q hstep hcase
        obtain ⟨g, hg, hgn, hgc⟩ := good_extend hn hf (by rw [hfn]; exact hstep) (by omega)
        exact ⟨g, hg, hgn, by omega⟩

/-! ### The number of markings is unbounded -/

theorem markCount_unbounded {p : Pos Q} {t0 : ℕ}
    (hmarks : {n | (treeRun B w n).mark p}.Infinite) (N : ℕ) :
    ∃ n, t0 ≤ n ∧ N ≤ markCount B w p t0 n := by
  classical
  have hinf : {n | (treeRun B w n).mark p} \ Set.Iic t0 |>.Infinite :=
    hmarks.diff (Set.finite_Iic t0)
  obtain ⟨s, hs, hcard⟩ := hinf.exists_subset_card_eq N
  rcases s.eq_empty_or_nonempty with rfl | hne
  · exact ⟨t0, le_refl _, by simp at hcard; omega⟩
  · obtain ⟨n, hn, hmax⟩ := s.exists_max_image id hne
    refine ⟨n, ?_, ?_⟩
    · have := hs hn
      simp only [Set.mem_diff, Set.mem_Iic, not_le] at this
      omega
    · rw [← hcard]
      refine Finset.card_le_card ?_
      intro m hm
      have hmem := hs hm
      simp only [Set.mem_diff, Set.mem_setOf_eq, Set.mem_Iic, not_le] at hmem
      simp only [Finset.mem_filter, Finset.mem_Ioc]
      exact ⟨⟨hmem.2, hmax m hm⟩, hmem.1⟩

/-! ### Soundness -/

/-- **Soundness of Safra's construction.**  If a node is present from some time on and is
marked infinitely often, then the Büchi automaton accepts the word. -/
theorem accepts_of_node {p : Pos Q} {t0 : ℕ}
    (halive : ∀ n, t0 ≤ n → labAt B w p n ≠ ∅) (hchild0 : childUnion B w p t0 = ∅)
    (hmarks : {n | (treeRun B w n).mark p}.Infinite) : B.Accepts w := by
  classical
  -- the property of a triple (time, state, number of visits of the Büchi set)
  set Pgood : ℕ × Q × ℕ → Prop := fun x =>
    ∃ f, GoodRun B w p t0 x.1 f ∧ f x.1 = x.2.1 ∧ x.2.2 = finCount B f t0 x.1 with hPgood
  -- one step backwards
  have key : ∀ x : ℕ × Q × ℕ, ∃ y : ℕ × Q × ℕ, Pgood x → t0 < x.1 →
      (y.1 + 1 = x.1 ∧ Pgood y ∧ B.step y.2.1 (w y.1) x.2.1 ∧
        x.2.2 = y.2.2 + (if y.2.1 ∈ B.fin then 1 else 0)) := by
    intro x
    by_cases hx : Pgood x ∧ t0 < x.1
    · obtain ⟨⟨f, hf, hfx, hcx⟩, hlt⟩ := hx
      obtain ⟨m, hm⟩ : ∃ m, x.1 = m + 1 := ⟨x.1 - 1, by omega⟩
      refine ⟨(m, f m, finCount B f t0 m), fun _ _ => ⟨by omega, ⟨f, hf.mono (by omega), rfl, rfl⟩,
        ?_, ?_⟩⟩
      · have := hf.2.1 m (by omega) (by omega)
        rw [← hfx, hm]
        exact this
      · rw [hcx, hm, finCount_succ B f (by omega)]
    · exact ⟨x, fun h1 h2 => absurd ⟨h1, h2⟩ hx⟩
  choose r hr using key
  -- the levels of the Kőnig argument
  set S : ℕ → Set (ℕ × Q × ℕ) := fun k => {x | x.1 = t0 + k ∧ Pgood x} with hS
  have hne : ∀ k, (S k).Nonempty := by
    intro k
    obtain ⟨q, hq⟩ := Set.nonempty_iff_ne_empty.2 (halive (t0 + k) (by omega))
    obtain ⟨f, hf, hfn⟩ := (exists_goodRun halive hchild0 (t0 + k) (by omega)).1 q hq
    exact ⟨(t0 + k, q, finCount B f t0 (t0 + k)), rfl, ⟨f, hf, hfn, rfl⟩⟩
  have hfin : ∀ k, (S k).Finite := by
    intro k
    refine Set.Finite.subset
      ((Set.finite_Iic (t0 + k)).prod ((Set.finite_univ (α := Q)).prod
        (Set.finite_Iic (t0 + k)))) ?_
    rintro ⟨n, q, cc⟩ ⟨hn, f, hf, hfn, hc⟩
    have hn' : n = t0 + k := hn
    have hc' : cc = finCount B f t0 n := hc
    have hcle : cc ≤ t0 + k := by
      rw [hc', hn']
      exact finCount_le B f t0 (t0 + k)
    refine ⟨?_, Set.mem_univ _, ?_⟩
    · simp only [Set.mem_Iic]
      omega
    · simpa only [Set.mem_Iic] using hcle
  have hstepS : ∀ k, ∀ x ∈ S (k + 1), r x ∈ S k := by
    intro k x hx
    obtain ⟨hx1, hxg⟩ := hx
    obtain ⟨h1, h2, -, -⟩ := hr x hxg (by omega)
    exact ⟨by omega, h2⟩
  obtain ⟨c, hcS, hcr⟩ := exists_coherent_seq S r hne hfin hstepS
  have hc1 : ∀ k, (c k).1 = t0 + k := fun k => (hcS k).1
  -- the run and the counter
  obtain ⟨rho, cnt, hrc⟩ : ∃ (rho : ℕ → Q) (cnt : ℕ → ℕ), ∀ k, c k = (t0 + k, rho k, cnt k) :=
    ⟨fun k => (c k).2.1, fun k => (c k).2.2, fun k => by rw [← hc1 k]⟩
  have hPg : ∀ k, Pgood (t0 + k, rho k, cnt k) := fun k => by rw [← hrc k]; exact (hcS k).2
  have hkey : ∀ k, B.step (rho k) (w (t0 + k)) (rho (k + 1)) ∧
      cnt (k + 1) = cnt k + (if rho k ∈ B.fin then 1 else 0) := by
    intro k
    obtain ⟨-, -, hstep', hcount'⟩ := hr (c (k + 1)) (hcS (k + 1)).2 (by rw [hc1]; omega)
    rw [hcr k, hrc k, hrc (k + 1)] at hstep' hcount'
    exact ⟨hstep', hcount'⟩
  -- the counter is unbounded
  have hcntge : ∀ k, markCount B w p t0 (t0 + k) ≤ cnt k := by
    intro k
    obtain ⟨f, hf, hfn, hc⟩ := hPg k
    rw [show cnt k = (((t0 + k, rho k, cnt k) : ℕ × Q × ℕ)).2.2 from rfl, hc]
    exact hf.2.2 (t0 + k) (by omega) (le_refl _)
  have hvisits : {k | rho k ∈ B.fin}.Infinite := by
    by_contra hfin'
    rw [Set.not_infinite] at hfin'
    obtain ⟨K, hK⟩ := hfin'.bddAbove
    have hconst : ∀ k, K + 1 ≤ k → cnt (k + 1) = cnt k := by
      intro k hk
      have hnm : rho k ∉ B.fin := by
        intro hmem
        have := hK (show k ∈ {k | rho k ∈ B.fin} from hmem)
        omega
      rw [(hkey k).2, if_neg hnm, Nat.add_zero]
    have hbdd : ∀ k, K + 1 ≤ k → cnt k = cnt (K + 1) := by
      intro k hk
      induction k, hk using Nat.le_induction with
      | base => rfl
      | succ k hk ih => rw [hconst k hk, ih]
    obtain ⟨n, hn, hNn⟩ := markCount_unbounded (p := p) (t0 := t0) hmarks (cnt (K + 1) + 1)
    have hle : markCount B w p t0 (t0 + (max (n - t0) (K + 1))) ≤ cnt (max (n - t0) (K + 1)) :=
      hcntge _
    rw [hbdd _ (le_max_right _ _)] at hle
    have hmono : markCount B w p t0 n ≤ markCount B w p t0 (t0 + max (n - t0) (K + 1)) := by
      unfold markCount
      refine Finset.card_le_card (Finset.filter_subset_filter _ ?_)
      refine Finset.Ioc_subset_Ioc_right ?_
      have := le_max_left (n - t0) (K + 1)
      omega
    omega
  -- the beginning of the run
  have hroot : rho 0 ∈ (treeRun B w t0).lab [] := by
    obtain ⟨f, hf, hfn, -⟩ := hPg 0
    have hfn' : f t0 = rho 0 := hfn
    have h0 : rho 0 ∈ labAt B w p t0 := by
      rw [← hfn']
      exact hf.1
    exact (inv_treeRun B w t0).mono' List.nil_suffix h0
  obtain ⟨g, hg0, hgt, hgrun⟩ := (mem_root_iff B w t0 (rho 0)).1 hroot
  refine ⟨fun n => if n ≤ t0 then g n else rho (n - t0), ⟨?_, ?_⟩, ?_⟩
  · show (if (0 : ℕ) ≤ t0 then g 0 else rho (0 - t0)) ∈ B.start
    rw [if_pos (Nat.zero_le _)]
    exact hg0
  · intro n
    show B.step (if n ≤ t0 then g n else rho (n - t0)) (w n)
      (if n + 1 ≤ t0 then g (n + 1) else rho (n + 1 - t0))
    rcases lt_trichotomy n t0 with hlt | heq | hgt
    · rw [if_pos (by omega : n ≤ t0), if_pos (by omega : n + 1 ≤ t0)]
      exact hgrun n (Nat.zero_le _) hlt
    · subst heq
      rw [if_pos (le_refl n), if_neg (by omega : ¬ (n + 1 ≤ n)),
        show n + 1 - n = 1 from by omega, hgt]
      have h := (hkey 0).1
      rw [Nat.add_zero] at h
      exact h
    · rw [if_neg (by omega : ¬ (n ≤ t0)), if_neg (by omega : ¬ (n + 1 ≤ t0)),
        show n + 1 - t0 = (n - t0) + 1 from by omega]
      have h := (hkey (n - t0)).1
      rw [show t0 + (n - t0) = n from by omega] at h
      exact h
  · refine Set.Infinite.mono (s := (fun k => t0 + k) '' ({k | rho k ∈ B.fin} \ {0})) ?_ ?_
    · rintro n ⟨k, ⟨hk, hk0⟩, rfl⟩
      simp only [Set.mem_setOf_eq, Set.mem_singleton_iff] at hk hk0
      show (if t0 + k ≤ t0 then g (t0 + k) else rho (t0 + k - t0)) ∈ B.fin
      rw [if_neg (by omega), show t0 + k - t0 = k from by omega]
      exact hk
    · exact Set.Infinite.image (fun a _ b _ hab => by omega)
        (hvisits.diff (Set.finite_singleton 0))

end Safra

end Lax369799Proofs.WordAutomata
