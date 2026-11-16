/-
Adapted from the Lean ancillary files of Bojańczyk, Casares, Manthe and
Parys, arXiv:2611.10136v1 (2026), with incorporation authorized by the user.
Original module: BorelMSO.Emptiness.Attractor.
Changes: Archive module paths and namespaces; port to the pinned toolchain.
See external-proofs.json for source provenance.
-/
import Mathlib.Data.Nat.Lattice
import Mathlib.Tactic.NormNum
import Lax369799Proofs.ParityGames

/-!
# Attractors

The *attractor* of Eve to a set of vertices `T` inside a subgame `S` is the set of vertices
from which Eve can force the play to visit `T`.  It is computed by the usual fixpoint
iteration: a vertex of Eve enters the attractor as soon as one of its successors is already
in it, and a vertex of Adam as soon as all its successors (inside `S`) are.

We prove the properties that Zielonka's induction needs:

* Eve has a positional strategy which, from any vertex of the attractor, forces the play to
  reach `T` (`reach_target`);
* the complement `S \ attr` is again a subgame (`closed_diff_attr`), and Eve cannot leave it
  towards the attractor (`eve_no_escape`).

Adam's attractor is obtained by applying the construction to the dual arena.
-/

namespace Lax369799Proofs.WordAutomata

namespace FinGame

namespace Arena

variable {V : Type} (a : Arena V) (S T : Set V)

/-- One step of the attractor computation. -/
def attrStep (X : Set V) : Set V :=
  X ∪ {v | v ∈ S ∧ ((a.own v ∧ ∃ w, w ∈ S ∧ a.E v w ∧ w ∈ X) ∨
    (¬ a.own v ∧ ∀ w, w ∈ S → a.E v w → w ∈ X))}

/-- The iterates of the attractor computation. -/
def attrIt (b : Arena V) (S' T' : Set V) : ℕ → Set V
  | 0 => T' ∩ S'
  | n + 1 => b.attrStep S' (attrIt b S' T' n)

/-- The attractor of `T` inside `S`, for Eve. -/
def attr : Set V := ⋃ n, a.attrIt S T n

/-- The rank of a vertex: the first stage of the iteration at which it appears. -/
noncomputable def attrRank (v : V) : ℕ := sInf {n | v ∈ a.attrIt S T n}

variable {a S T}

theorem attrIt_mono {m n : ℕ} (h : m ≤ n) : a.attrIt S T m ⊆ a.attrIt S T n := by
  induction n with
  | zero =>
      have : m = 0 := Nat.le_zero.1 h
      subst this
      exact subset_rfl
  | succ k ih =>
      rcases Nat.lt_or_ge m (k + 1) with hm | hm
      · exact fun x hx => Or.inl (ih (Nat.lt_succ_iff.1 hm) hx)
      · have : m = k + 1 := le_antisymm h hm
        subst this
        exact subset_rfl

theorem attrIt_subset (n : ℕ) : a.attrIt S T n ⊆ S := by
  induction n with
  | zero => exact fun x hx => hx.2
  | succ k ih =>
      rintro x (hx | hx)
      · exact ih hx
      · exact hx.1

theorem attr_subset : a.attr S T ⊆ S := by
  rintro x hx
  obtain ⟨n, hx⟩ := Set.mem_iUnion.1 hx
  exact attrIt_subset n hx

theorem mem_attr_iff {v : V} : v ∈ a.attr S T ↔ ∃ n, v ∈ a.attrIt S T n := Set.mem_iUnion

theorem target_subset_attr : T ∩ S ⊆ a.attr S T := fun _ hx => mem_attr_iff.2 ⟨0, hx⟩

theorem mem_attrIt_of_le {v : V} {n m : ℕ} (h : v ∈ a.attrIt S T n) (hn : n ≤ m) :
    v ∈ a.attrIt S T m := attrIt_mono hn h

theorem mem_attrIt_attrRank {v : V} (hv : v ∈ a.attr S T) :
    v ∈ a.attrIt S T (a.attrRank S T v) :=
  Nat.sInf_mem (mem_attr_iff.1 hv)

theorem attrRank_le {v : V} {n : ℕ} (h : v ∈ a.attrIt S T n) : a.attrRank S T v ≤ n :=
  Nat.sInf_le h

theorem not_mem_attrIt_of_lt_attrRank {v : V} {n : ℕ} (h : n < a.attrRank S T v) :
    v ∉ a.attrIt S T n := fun hc => absurd (attrRank_le hc) (by omega)

theorem mem_target_of_attrRank_zero {v : V} (hv : v ∈ a.attr S T)
    (h : a.attrRank S T v = 0) : v ∈ T := by
  have := mem_attrIt_attrRank hv
  rw [h] at this
  exact this.1

/-- The defining property of a vertex of the attractor which is not yet in the target. -/
theorem attr_step_prop {v : V} (hv : v ∈ a.attr S T) (hvT : v ∉ T) :
    (a.own v → ∃ w, w ∈ S ∧ a.E v w ∧ w ∈ a.attr S T ∧
        a.attrRank S T w < a.attrRank S T v) ∧
    (¬ a.own v → ∀ w, w ∈ S → a.E v w → w ∈ a.attr S T ∧
        a.attrRank S T w < a.attrRank S T v) := by
  have hr : a.attrRank S T v ≠ 0 := by
    intro h
    exact hvT (mem_target_of_attrRank_zero hv h)
  obtain ⟨k, hk⟩ : ∃ k, a.attrRank S T v = k + 1 := ⟨a.attrRank S T v - 1, by omega⟩
  have hmem : v ∈ a.attrIt S T (k + 1) := by
    have := mem_attrIt_attrRank hv
    rwa [hk] at this
  have hnot : v ∉ a.attrIt S T k := not_mem_attrIt_of_lt_attrRank (by omega)
  rcases hmem with h | h
  · exact absurd h hnot
  · rcases h.2 with ⟨hown, w, hwS, hwE, hwX⟩ | ⟨hown, hall⟩
    · refine ⟨fun _ => ⟨w, hwS, hwE, mem_attr_iff.2 ⟨k, hwX⟩, ?_⟩, fun hc => absurd hown hc⟩
      have := attrRank_le hwX
      omega
    · refine ⟨fun hc => absurd hc hown, fun _ w hwS hwE => ?_⟩
      have hw := hall w hwS hwE
      exact ⟨mem_attr_iff.2 ⟨k, hw⟩, by have := attrRank_le hw; omega⟩

/-- Eve has a positional strategy that decreases the attractor rank. -/
theorem exists_attrStrat (hS : a.Closed S) :
    ∃ f, a.EveOK S f ∧ ∀ v, v ∈ a.attr S T → v ∉ T → a.own v →
      f v ∈ a.attr S T ∧ a.attrRank S T (f v) < a.attrRank S T v := by
  classical
  have key : ∀ v : V, ∃ w, (v ∈ S → a.own v → w ∈ S ∧ a.E v w) ∧
      (v ∈ a.attr S T → v ∉ T → a.own v →
        w ∈ a.attr S T ∧ a.attrRank S T w < a.attrRank S T v) := by
    intro v
    by_cases hcase : v ∈ a.attr S T ∧ v ∉ T ∧ a.own v
    · obtain ⟨w, hwS, hwE, hwA, hwr⟩ := (attr_step_prop hcase.1 hcase.2.1).1 hcase.2.2
      exact ⟨w, fun _ _ => ⟨hwS, hwE⟩, fun _ _ _ => ⟨hwA, hwr⟩⟩
    · by_cases hvS : v ∈ S
      · obtain ⟨w, hwS, hwE⟩ := hS v hvS
        refine ⟨w, fun _ _ => ⟨hwS, hwE⟩, fun h1 h2 h3 => absurd ⟨h1, h2, h3⟩ hcase⟩
      · exact ⟨v, fun hc => absurd hc hvS, fun h1 h2 h3 => absurd ⟨h1, h2, h3⟩ hcase⟩
  choose f hf using key
  exact ⟨f, fun v hvS hown => (hf v).1 hvS hown, fun v h1 h2 h3 => (hf v).2 h1 h2 h3⟩

/-- Adam's moves inside the attractor also decrease the rank. -/
theorem attr_adam_succ {v w : V} (hv : v ∈ a.attr S T) (hvT : v ∉ T) (hown : ¬ a.own v)
    (hwS : w ∈ S) (hwE : a.E v w) :
    w ∈ a.attr S T ∧ a.attrRank S T w < a.attrRank S T v :=
  (attr_step_prop hv hvT).2 hown w hwS hwE

/-- From the attractor, Eve's attractor strategy forces the play to reach the target. -/
theorem reach_target {f : V → V} (hf : ∀ v, v ∈ a.attr S T → v ∉ T → a.own v →
      f v ∈ a.attr S T ∧ a.attrRank S T (f v) < a.attrRank S T v)
    {π : ℕ → V} (hπ : a.PathIn S π) (h0 : π 0 ∈ a.attr S T)
    (hcons : ∀ n, π n ∈ a.attr S T → π n ∉ T → a.own (π n) → π (n + 1) = f (π n)) :
    ∃ n, π n ∈ T := by
  classical
  -- strong induction on the rank of the starting vertex
  suffices H : ∀ r : ℕ, ∀ π : ℕ → V, a.PathIn S π → π 0 ∈ a.attr S T →
      a.attrRank S T (π 0) ≤ r →
      (∀ n, π n ∈ a.attr S T → π n ∉ T → a.own (π n) → π (n + 1) = f (π n)) →
      ∃ n, π n ∈ T by
    exact H (a.attrRank S T (π 0)) π hπ h0 le_rfl hcons
  intro r
  induction r using Nat.strong_induction_on with
  | _ r ih =>
    intro π hπ h0 hle hcons
    by_cases hT : π 0 ∈ T
    · exact ⟨0, hT⟩
    · have hnext : π 1 ∈ a.attr S T ∧ a.attrRank S T (π 1) < a.attrRank S T (π 0) := by
        by_cases hown : a.own (π 0)
        · have := hcons 0 h0 hT hown
          rw [this]
          exact hf (π 0) h0 hT hown
        · exact attr_adam_succ h0 hT hown (hπ.2 1) (hπ.1 0)
      have hlt : a.attrRank S T (π 1) < r := by omega
      have hzero : shift π 1 0 = π 1 := by
        show π (0 + 1) = π 1
        norm_num
      have hstep : ∀ n, shift π 1 n = π (n + 1) := by
        intro n
        show π (n + 1) = π (n + 1)
        rfl
      have hcons' : ∀ n, shift π 1 n ∈ a.attr S T → shift π 1 n ∉ T → a.own (shift π 1 n) →
          shift π 1 (n + 1) = f (shift π 1 n) := by
        intro n hn1 hn2 hn3
        rw [hstep n] at hn1 hn2 hn3 ⊢
        rw [hstep (n + 1)]
        exact hcons (n + 1) hn1 hn2 hn3
      obtain ⟨n, hn⟩ := ih _ hlt (shift π 1) (a.pathIn_shift hπ 1)
        (by rw [hzero]; exact hnext.1) (by rw [hzero]) hcons'
      exact ⟨n + 1, by rw [← hstep n]; exact hn⟩

/-- Eve cannot escape from the complement of her own attractor. -/
theorem eve_no_escape {v w : V} (hvS : v ∈ S) (hv : v ∉ a.attr S T) (hown : a.own v)
    (hwS : w ∈ S) (hwE : a.E v w) : w ∉ a.attr S T := by
  intro hw
  obtain ⟨n, hn⟩ := mem_attr_iff.1 hw
  exact hv (mem_attr_iff.2 ⟨n + 1, Or.inr ⟨hvS, Or.inl ⟨hown, w, hwS, hwE, hn⟩⟩⟩)

/-- From a vertex of Adam outside the attractor there is a move staying outside. -/
theorem adam_stay [Fintype V] {v : V} (hvS : v ∈ S)
    (hv : v ∉ a.attr S T) (hown : ¬ a.own v) :
    ∃ w, w ∈ S ∧ w ∉ a.attr S T ∧ a.E v w := by
  classical
  by_contra hcon
  push_neg at hcon
  -- every successor of `v` inside `S` is in the attractor, at some finite stage
  have hall : ∀ w, w ∈ S → a.E v w → w ∈ a.attr S T := by
    intro w hwS hwE
    by_contra hw
    exact hw (by
      have := hcon w hwS
      by_contra hc
      exact absurd hwE (this hc))
  -- since `V` is finite, one stage works for all successors
  obtain ⟨N, hN⟩ : ∃ N, ∀ w, w ∈ S → a.E v w → w ∈ a.attrIt S T N := by
    have hfun : ∀ w : V, ∃ n, w ∈ S → a.E v w → w ∈ a.attrIt S T n := by
      intro w
      by_cases hw : w ∈ S ∧ a.E v w
      · obtain ⟨n, hn⟩ := mem_attr_iff.1 (hall w hw.1 hw.2)
        exact ⟨n, fun _ _ => hn⟩
      · exact ⟨0, fun h1 h2 => absurd ⟨h1, h2⟩ hw⟩
    choose nn hnn using hfun
    refine ⟨(Finset.univ.image nn).sup id, fun w hwS hwE => ?_⟩
    exact mem_attrIt_of_le (hnn w hwS hwE)
      (Finset.le_sup (f := id) (Finset.mem_image_of_mem nn (Finset.mem_univ w)))
  exact hv (mem_attr_iff.2 ⟨N + 1, Or.inr ⟨hvS, Or.inr ⟨hown, hN⟩⟩⟩)

/-- The complement of the attractor is again a subgame. -/
theorem closed_diff_attr [Fintype V] (hS : a.Closed S) : a.Closed (S \ a.attr S T) := by
  rintro v ⟨hvS, hv⟩
  by_cases hown : a.own v
  · obtain ⟨w, hwS, hwE⟩ := hS v hvS
    exact ⟨w, ⟨hwS, eve_no_escape hvS hv hown hwS hwE⟩, hwE⟩
  · obtain ⟨w, hwS, hw, hwE⟩ := adam_stay hvS hv hown
    exact ⟨w, ⟨hwS, hw⟩, hwE⟩

end Arena

end FinGame

end Lax369799Proofs.WordAutomata
