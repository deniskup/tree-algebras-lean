/-
Adapted from the Lean ancillary files of Bojańczyk, Casares, Manthe and
Parys, arXiv:2611.10136v1 (2026), with incorporation authorized by the user.
Original module: BorelMSO.Safra.Main.
Changes: Archive module paths and namespaces; port to the pinned toolchain.
See external-proofs.json for source provenance.
-/
import Mathlib.Data.Set.Finite.List
import Lax369799Proofs.SafraSoundness
import Lax369799Proofs.SafraCompleteness

/-!
# Safra's determinization theorem, and McNaughton's theorem

This file puts together the two halves of the correctness of Safra's construction
(`Lax369799Proofs.WordAutomata/Safra/Sound.lean` and `Lax369799Proofs.WordAutomata/Safra/Complete.lean`) and derives:

* `Lax369799Proofs.WordAutomata.Safra.accepts_detAut_iff`: the deterministic Muller automaton
  `Lax369799Proofs.WordAutomata.Safra.detAut B` accepts exactly the ω-words accepted by the nondeterministic
  Büchi automaton `B`;
* `Lax369799Proofs.WordAutomata.buchiDeterminization`: **Safra's determinization theorem**;
* `Lax369799Proofs.WordAutomata.mcNaughton`: **McNaughton's determinization theorem**, obtained from Safra's
  theorem through the reduction of `Lax369799Proofs.WordAutomata/Automata/MullerToBuchi.lean`.

The states of the deterministic automaton are the Safra trees, presented as functions from
the positions of bounded length (a finite type) to pairs (label, mark).  The acceptance
condition is the Muller condition "some position is present in all the trees seen infinitely
often, and marked in one of them", which expresses that the position is present from some
time on and marked infinitely often.
-/

namespace Lax369799Proofs.WordAutomata

namespace Safra

open scoped Classical

variable {Q Gam : Type} [Fintype Q] {B : NBuchi Q Gam} {w : ℕ → Gam}

/-! ### A finite presentation of the Safra trees -/

/-- The positions of a Safra tree that can be present or marked. -/
def FPos (Q : Type) [Fintype Q] : Type := {p : Pos Q // p.length ≤ Fintype.card Q}

instance : Finite (FPos Q) :=
  (List.finite_length_le (Slot Q) (Fintype.card Q)).to_subtype

/-- The state space of the deterministic automaton: a Safra tree of bounded depth. -/
def SafraState (Q : Type) [Fintype Q] : Type := FPos Q → Set Q × Prop

instance : Finite (SafraState Q) := by
  unfold SafraState
  infer_instance

/-- A Safra tree in which every node of large depth is absent and unmarked. -/
def Vanishes (T : STree Q) : Prop :=
  ∀ p : Pos Q, Fintype.card Q < p.length → T.lab p = ∅ ∧ ¬ T.mark p

/-- The finite presentation of a Safra tree. -/
def restrictTree (T : STree Q) : SafraState Q := fun p => (T.lab p.1, T.mark p.1)

/-- The Safra tree described by a state of the deterministic automaton. -/
def extendState (s : SafraState Q) : STree Q where
  lab p := if h : p.length ≤ Fintype.card Q then (s ⟨p, h⟩).1 else ∅
  mark p := if h : p.length ≤ Fintype.card Q then (s ⟨p, h⟩).2 else False

theorem extendState_restrictTree {T : STree Q} (h : Vanishes T) :
    extendState (restrictTree T) = T := by
  have e1 : (extendState (restrictTree T)).lab = T.lab := by
    funext p
    show (if hp : p.length ≤ Fintype.card Q then T.lab p else ∅) = T.lab p
    by_cases hp : p.length ≤ Fintype.card Q
    · rw [dif_pos hp]
    · rw [dif_neg hp]
      exact ((h p (by omega)).1).symm
  have e2 : (extendState (restrictTree T)).mark = T.mark := by
    funext p
    show (if hp : p.length ≤ Fintype.card Q then T.mark p else False) = T.mark p
    by_cases hp : p.length ≤ Fintype.card Q
    · rw [dif_pos hp]
    · rw [dif_neg hp]
      exact propext ⟨False.elim, fun hc => absurd hc (h p (by omega)).2⟩
  have : extendState (restrictTree T) = STree.mk T.lab T.mark := by rw [← e1, ← e2]
  rw [this]

/-- Every tree of the run has bounded depth. -/
theorem vanishes_treeRun (B : NBuchi Q Gam) (w : ℕ → Gam) (n : ℕ) :
    Vanishes (treeRun B w n) := by
  intro p hp
  constructor
  · by_contra hc
    have := (inv_treeRun B w n).length_lt hc
    omega
  · match n with
    | 0 => exact id
    | n + 1 =>
        intro hm
        obtain ⟨hvm, -⟩ := hm
        obtain ⟨q, hq⟩ := hvm.1
        have := lab2_length_le (inv_treeRun B w n) hq
        omega

/-! ### The deterministic automaton -/

/-- **The deterministic Muller automaton produced by Safra's construction.** -/
noncomputable def detAut (B : NBuchi Q Gam) : DMuller (SafraState Q) Gam where
  start := restrictTree (initTree B)
  step s a := restrictTree (stepTree B (extendState s) a)
  acc F := ∃ p : FPos Q, (∀ s ∈ F, (s p).1 ≠ ∅) ∧ ∃ s ∈ F, (s p).2

theorem run_detAut (B : NBuchi Q Gam) (w : ℕ → Gam) (n : ℕ) :
    (detAut B).run w n = restrictTree (treeRun B w n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      show restrictTree (stepTree B (extendState ((detAut B).run w n)) (w n)) = _
      rw [ih, extendState_restrictTree (vanishes_treeRun B w n)]
      rfl

/-! ### Correctness -/

/-- If a state occurs infinitely often in the run of the deterministic automaton, then it
occurs at arbitrarily late times. -/
theorem exists_late_time {s : SafraState Q} (hs : s ∈ (detAut B).infStates w) (N : ℕ) :
    ∃ n, N ≤ n ∧ (detAut B).run w n = s := by
  obtain ⟨n, hn, hn'⟩ := (hs.diff (Set.finite_Iic N)).nonempty
  simp only [Set.mem_Iic, not_le] at hn'
  exact ⟨n, by omega, hn⟩

/-- From some time on, the run of the deterministic automaton only visits states occurring
infinitely often. -/
theorem eventually_mem_infStates (B : NBuchi Q Gam) (w : ℕ → Gam) :
    ∃ N, ∀ n, N ≤ n → (detAut B).run w n ∈ (detAut B).infStates w := by
  classical
  have hfin : {n | (detAut B).run w n ∉ (detAut B).infStates w}.Finite := by
    have hsplit : {n | (detAut B).run w n ∉ (detAut B).infStates w} =
        ⋃ s ∈ {s : SafraState Q | s ∉ (detAut B).infStates w}, {n | (detAut B).run w n = s} := by
      ext n
      simp only [Set.mem_setOf_eq, Set.mem_iUnion, exists_prop]
      exact ⟨fun hn => ⟨_, hn, rfl⟩, fun ⟨s, hs, hn⟩ => by rw [hn]; exact hs⟩
    rw [hsplit]
    refine Set.Finite.biUnion (Set.toFinite _) (fun s hs => ?_)
    simpa [DMuller.infStates, Set.not_infinite] using hs
  obtain ⟨M, hM⟩ := hfin.bddAbove
  refine ⟨M + 1, fun n hn => ?_⟩
  by_contra hc
  have := hM (show n ∈ {n | (detAut B).run w n ∉ (detAut B).infStates w} from hc)
  omega

/-- **Correctness of Safra's construction.** -/
theorem accepts_detAut_iff (B : NBuchi Q Gam) (w : ℕ → Gam) :
    (detAut B).Accepts w ↔ B.Accepts w := by
  classical
  constructor
  · rintro ⟨p, hpres, s0, hs0, hs0m⟩
    -- the node `p` is present from some time on
    obtain ⟨N, hN⟩ := eventually_mem_infStates B w
    have halive : ∀ n, N ≤ n → (treeRun B w n).lab p.1 ≠ ∅ := by
      intro n hn
      have h1 := hpres _ (hN n hn)
      rw [run_detAut] at h1
      exact h1
    -- and it is marked infinitely often
    have hmarks : {n | (treeRun B w n).mark p.1}.Infinite := by
      refine Set.Infinite.mono (s := {n | (detAut B).run w n = s0}) ?_ hs0
      intro n hn
      simp only [Set.mem_setOf_eq] at hn ⊢
      have : (restrictTree (treeRun B w n) p).2 := by
        rw [← run_detAut, hn]; exact hs0m
      exact this
    -- pick a marking time after `N`; at that time `p` has no child
    obtain ⟨t0, ht0, ht0N⟩ : ∃ t0, (treeRun B w t0).mark p.1 ∧ N + 1 ≤ t0 := by
      obtain ⟨t, ht, ht'⟩ := (hmarks.diff (Set.finite_Iic (N + 1))).nonempty
      simp only [Set.mem_Iic, not_le] at ht'
      exact ⟨t, ht, by omega⟩
    obtain ⟨t1, rfl⟩ : ∃ t1, t0 = t1 + 1 := ⟨t0 - 1, by omega⟩
    refine accepts_of_node (p := p.1) (t0 := t1 + 1) (fun n hn => halive n (by omega)) ?_ hmarks
    exact childUnion_eq_empty_of_mark ht0
  · intro hacc
    obtain ⟨p, N, halive, hmarks⟩ := exists_node_of_accepts hacc
    have hlen : p.length ≤ Fintype.card Q :=
      le_of_lt ((inv_treeRun B w N).length_lt (halive N (le_refl N)))
    refine ⟨⟨p, hlen⟩, ?_, ?_⟩
    · intro s hs
      obtain ⟨n, hn, hns⟩ := exists_late_time hs N
      rw [← hns, run_detAut]
      exact halive n hn
    · -- some state occurring infinitely often is marked at `p`
      have hex : ∃ s : SafraState Q,
          {n | (treeRun B w n).mark p ∧ (detAut B).run w n = s}.Infinite := by
        by_contra hcon
        push_neg at hcon
        have hsplit : {n | (treeRun B w n).mark p} =
            ⋃ s : SafraState Q, {n | (treeRun B w n).mark p ∧ (detAut B).run w n = s} := by
          ext n
          simp only [Set.mem_setOf_eq, Set.mem_iUnion]
          exact ⟨fun hn => ⟨_, hn, rfl⟩, fun h => h.elim (fun _ hs => hs.1)⟩
        refine hmarks ?_
        rw [hsplit]
        exact Set.finite_iUnion hcon
      obtain ⟨s, hs⟩ := hex
      refine ⟨s, ?_, ?_⟩
      · exact Set.Infinite.mono (fun n hn => hn.2) hs
      · obtain ⟨n, hn1, hn2⟩ := hs.nonempty
        rw [← hn2, run_detAut]
        exact hn1

end Safra

/-- **Safra's determinization theorem.**  Every language of ω-words recognized by a
nondeterministic Büchi automaton with finitely many states is recognized by a deterministic
Muller automaton. -/
theorem buchiDeterminization : BuchiDeterminization := by
  intro S Gam hS _ B
  haveI : Fintype S := Fintype.ofFinite S
  exact ⟨Safra.SafraState S, inferInstance, Safra.detAut B, Safra.accepts_detAut_iff B⟩

/-- **McNaughton's determinization theorem.**  Every language of ω-words recognized by a
nondeterministic Muller automaton with finitely many states is recognized by a deterministic
Muller automaton. -/
theorem mcNaughton : McNaughton := mcNaughton_of_buchiDeterminization buchiDeterminization

end Lax369799Proofs.WordAutomata
