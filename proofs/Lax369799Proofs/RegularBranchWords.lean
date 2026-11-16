import Lax369799.RegularBranchWords
import Lax369799Proofs.RunBranchObservations
import Lax369799Proofs.UnfoldBranches

namespace Lax369799Proofs.RegularBranchWords
open Lax369799.RankedSystems (RankedSet System)
open Lax369799.UnfoldAutomata Lax369799.RunBranchObservations Lax369799.RegularBranchWords

/--
---
conclusion: Lax369799.RegularBranchWords.periodic
---
A finite functional graph has an ultimately periodic orbit. The branch's
vertices and directions are functions of that orbit.
-/
theorem periodic {A : RankedSet} {S : System A 0} (b : RegularBranch S) :
    Lax369799.UnfoldBranches.Periodic (trace b) := by
  have hc : Lax369799.WordParity.LeastRecurring (fun _ : ℕ => 0) 0 :=
    ⟨fun N => ⟨N, le_rfl, rfl⟩, fun a ha => by omega⟩
  obtain ⟨s, hs, he, hp, _⟩ := PeriodicPaths.periodic_witness
    (fun x y => b.next x = y) (fun _ => 0) (position b) (fun _ => rfl) 0 hc
  have hseq (n : ℕ) : s n = position b n := by
    induction n with
    | zero => exact hs
    | succ n ih => exact (he n).symm.trans (congrArg b.next ih)
  obtain ⟨N, p, hp, hperiod⟩ := hp
  refine ⟨N, p, hp, ?_⟩
  intro n hn
  change (⟨b.vertex (position b (n + p)), b.direction (position b (n + p))⟩ :
    (v : S.val.Vertex) × Fin (Rank S v)) = _
  have h := hperiod n hn
  rw [hseq, hseq] at h
  exact congrArg (fun i => (⟨b.vertex i, b.direction i⟩ :
    (v : S.val.Vertex) × Fin (Rank S v))) h

private theorem index_value {Q : Type} (w : ℕ → Q) {N p : ℕ} (hp : 0 < p)
    (hw : ∀ n, N ≤ n → w (n + p) = w n) (n : ℕ) :
    w (PeriodicPaths.index N (N + p) n) = w n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hN : n < N
    · simp [PeriodicPaths.index, hN]
    · by_cases hnp : n < N + p
      · simp only [PeriodicPaths.index, if_neg hN, Nat.add_sub_cancel_left,
          Nat.mod_eq_of_lt (by omega : n - N < p)]
        congr 1
        omega
      · have hsmall : n - p < n := by omega
        have hlarge : N ≤ n - p := by omega
        have hidx : PeriodicPaths.index N (N + p) n =
            PeriodicPaths.index N (N + p) (n - p) := by
          simp only [PeriodicPaths.index, if_neg hN, if_neg (by omega : ¬n - p < N),
            Nat.add_sub_cancel_left]
          have hh : n - N = (n - p - N) + p := by omega
          rw [hh, Nat.add_mod_right]
        rw [hidx, ih _ hsmall, ← hw (n - p) hlarge]
        congr 1
        omega

/--
---
conclusion: Lax369799.RegularBranchWords.represents
---
Retain the prefix and one period, then redirect the last edge to the
start of the period. Periodicity includes directions as well as vertices.
-/
theorem represents {A : RankedSet} {S : System A 0} (b : InfiniteBranch S)
    (hb : Lax369799.UnfoldBranches.Periodic b) :
    ∃ c : RegularBranch S, ∀ n,
      (⟨(trace c).vertex n, (trace c).direction n⟩ : (v : S.val.Vertex) × Fin (Rank S v)) =
        ⟨b.vertex n, b.direction n⟩ := by
  obtain ⟨N, p, hp, hb⟩ := hb
  let next : Fin (N + p) → Fin (N + p) := fun i =>
    if h : i.val + 1 < N + p then ⟨i.val + 1, h⟩ else ⟨N, by omega⟩
  let c : RegularBranch S := {
    size := N + p
    start := ⟨0, by omega⟩
    next := next
    vertex := fun i => b.vertex i.val
    direction := fun i => b.direction i.val
    starts := b.starts
    follows := by
      intro i
      by_cases hi : i.val + 1 < N + p
      · simpa only [next, dif_pos hi] using b.follows i.val
      · have he : i.val + 1 = N + p := by have := i.isLt; omega
        have hv := congrArg Sigma.fst (hb N le_rfl)
        change b.vertex (N + p) = b.vertex N at hv
        have h := b.follows i.val
        simpa only [next, dif_neg hi, he, hv] using h }
  have hpos (n : ℕ) : (position c n).val = PeriodicPaths.index N (N + p) n := by
    induction n with
    | zero => exact (PeriodicPaths.index_zero N (N + p)).symm
    | succ n ih =>
      change (next (position c n)).val = _
      rcases PeriodicPaths.index_succ (by omega : N < N + p) n with he | ⟨he, he'⟩
      · have hlt : PeriodicPaths.index N (N + p) (n + 1) < N + p := by
          by_cases hn : n + 1 < N
          · simp only [PeriodicPaths.index, if_pos hn]; omega
          · exact (PeriodicPaths.index_bounds (by omega : N < N + p) (by omega)).2
        have hi : (position c n).val + 1 < N + p := by omega
        simp only [next, dif_pos hi, ih, he]
      · have hi : ¬ (position c n).val + 1 < N + p := by omega
        simp only [next, dif_neg hi, he']
  refine ⟨c, ?_⟩
  intro n
  change (⟨b.vertex (position c n).val, b.direction (position c n).val⟩ :
    (v : S.val.Vertex) × Fin (Rank S v)) = _
  rw [hpos]
  exact index_value (fun n => (⟨b.vertex n, b.direction n⟩ :
    (v : S.val.Vertex) × Fin (Rank S v))) hp hb n

/--
---
conclusion: Lax369799.RegularBranchWords.regular_test
---
Present every ultimately periodic branch by its finite graph, then apply
the periodic branch test for the parity condition.
-/
theorem regular_test {A : RankedSet} (M : UnfoldAutomaton A) (S : System A 0) (r : Run M S) :
    (∀ b : RegularBranch S, M.condition.AcceptsInfinite
      (fun n => r.edgeType ((trace b).vertex n) ((trace b).direction n))) ↔
    (∀ b : InfiniteBranch S, M.condition.AcceptsInfinite
      (fun n => r.edgeType (b.vertex n) (b.direction n))) := by
  constructor
  · intro h
    apply (UnfoldBranches.periodic_test M S r).mp
    intro b hb
    obtain ⟨c, hc⟩ := represents b hb
    have hw : (fun n => r.edgeType ((trace c).vertex n) ((trace c).direction n)) =
        (fun n => r.edgeType (b.vertex n) (b.direction n)) := by
      funext n
      exact congrArg (fun v : (v : S.val.Vertex) × Fin (Rank S v) => r.edgeType v.1 v.2) (hc n)
    simpa only [hw] using h c
  · exact fun h b => h (trace b)

end Lax369799Proofs.RegularBranchWords
