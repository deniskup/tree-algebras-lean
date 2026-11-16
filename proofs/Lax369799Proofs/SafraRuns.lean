/-
Adapted from the Lean ancillary files of Bojańczyk, Casares, Manthe and
Parys, arXiv:2611.10136v1 (2026), with incorporation authorized by the user.
Original module: BorelMSO.Safra.Run.
Changes: Archive module paths and namespaces; port to the pinned toolchain.
See external-proofs.json for source provenance.
-/
import Lax369799Proofs.SafraTrees

/-!
# The run of Safra's construction

This file introduces the initial Safra tree and the sequence of Safra trees obtained by
reading an ω-word (`Lax369799Proofs.WordAutomata.Safra.treeRun`), records that the invariants hold all along
the run, and proves the two elementary facts about it which are used in both directions of
the correctness proof:

* the label of the root at time `n` is the set of states reachable from the initial states
  by a partial run of length `n` (`Lax369799Proofs.WordAutomata.Safra.mem_root_iff`);
* every state of the label of a node at time `n + 1` comes from a state of the label of the
  parent at time `n`, and it comes from the node itself unless the parent was in the Büchi
  set (`Lax369799Proofs.WordAutomata.Safra.mem_lab1_cons`).
-/

namespace Lax369799Proofs.WordAutomata

namespace Safra

open scoped Classical

variable {Q Gam : Type} [Fintype Q]

/-- The initial Safra tree: only the root is present, with the set of initial states as
label. -/
def initTree (B : NBuchi Q Gam) : STree Q where
  lab p := if p = [] then B.start else ∅
  mark _ := False

@[simp] theorem initTree_lab_nil (B : NBuchi Q Gam) : (initTree B).lab [] = B.start := rfl

@[simp] theorem initTree_lab_cons (B : NBuchi Q Gam) (i : Slot Q) (p : Pos Q) :
    (initTree B).lab (i :: p) = ∅ := rfl

theorem inv_initTree (B : NBuchi Q Gam) : Inv (initTree B) where
  mono i p := by simp
  disj p _ := by simp
  ssub i p h := by simp at h

/-- The sequence of Safra trees produced by reading an ω-word. -/
noncomputable def treeRun (B : NBuchi Q Gam) (w : ℕ → Gam) : ℕ → STree Q
  | 0 => initTree B
  | n + 1 => stepTree B (treeRun B w n) (w n)

@[simp] theorem treeRun_zero (B : NBuchi Q Gam) (w : ℕ → Gam) :
    treeRun B w 0 = initTree B := rfl

@[simp] theorem treeRun_succ (B : NBuchi Q Gam) (w : ℕ → Gam) (n : ℕ) :
    treeRun B w (n + 1) = stepTree B (treeRun B w n) (w n) := rfl

theorem inv_treeRun (B : NBuchi Q Gam) (w : ℕ → Gam) : ∀ n, Inv (treeRun B w n)
  | 0 => inv_initTree B
  | n + 1 => inv_stepTree B (treeRun B w n) (w n)

/-! ### Elementary properties of one step -/

theorem not_killed_nil (B : NBuchi Q Gam) (T : STree Q) (a : Gam) : ¬ killed B T a [] := by
  rintro ⟨c, hc, hcne, -⟩
  exact hcne (List.suffix_nil.1 hc)

theorem stepTree_lab_nil (B : NBuchi Q Gam) (T : STree Q) (a : Gam) :
    (stepTree B T a).lab [] = succSet B a (T.lab []) := by
  rw [stepTree_lab_of_not_killed B T a (not_killed_nil B T a), lab2_nil, lab1_nil]

/-- If a node is present, then its slot is not the fresh slot of its parent, so its new
label is computed from its own old label. -/
theorem lab1_cons_of_lab_ne (B : NBuchi Q Gam) (T : STree Q) (a : Gam) {i : Slot Q}
    {p : Pos Q} (h : T.lab (i :: p) ≠ ∅) :
    lab1 B T a (i :: p) = succSet B a (T.lab (i :: p)) := by
  refine lab1_cons_of_ne B T a ?_
  intro hfresh
  exact h (lab_eq_empty_of_freshSlot hfresh)

/-- Every state of the new label of a node comes from a state of the old label of the
parent; it comes from the old label of the node itself unless the parent was in the Büchi
set. -/
theorem mem_lab1_cons (B : NBuchi Q Gam) (T : STree Q) (a : Gam) {i : Slot Q} {p : Pos Q}
    {q : Q} (hq : q ∈ lab1 B T a (i :: p)) (hmono : T.lab (i :: p) ⊆ T.lab p) :
    ∃ q0 ∈ T.lab p, B.step q0 a q ∧ (q0 ∈ B.fin ∨ q0 ∈ T.lab (i :: p)) := by
  rw [lab1_cons] at hq
  split at hq
  · obtain ⟨q0, hq0, hstep⟩ := hq
    exact ⟨q0, hq0.1, hstep, Or.inl hq0.2⟩
  · obtain ⟨q0, hq0, hstep⟩ := hq
    exact ⟨q0, hmono hq0, hstep, Or.inr hq0⟩

theorem mem_lab1_nil (B : NBuchi Q Gam) (T : STree Q) (a : Gam) {q : Q}
    (hq : q ∈ lab1 B T a []) : ∃ q0 ∈ T.lab ([] : Pos Q), B.step q0 a q := hq

/-! ### Partial runs -/

/-- `PRun B w s t f` says that `f` follows the transitions of `B` on the letters of `w`
between the times `s` and `t`. -/
def PRun (B : NBuchi Q Gam) (w : ℕ → Gam) (s t : ℕ) (f : ℕ → Q) : Prop :=
  ∀ k, s ≤ k → k < t → B.step (f k) (w k) (f (k + 1))

omit [Fintype Q] in
theorem PRun.mono {B : NBuchi Q Gam} {w : ℕ → Gam} {s s' t t' : ℕ} {f : ℕ → Q}
    (h : PRun B w s t f) (hs : s ≤ s') (ht : t' ≤ t) : PRun B w s' t' f :=
  fun k hk hk' => h k (le_trans hs hk) (lt_of_lt_of_le hk' ht)

omit [Fintype Q] in
theorem PRun.succ {B : NBuchi Q Gam} {w : ℕ → Gam} {s t : ℕ} {f : ℕ → Q} (h : PRun B w s t f)
    (hstep : B.step (f t) (w t) (f (t + 1))) : PRun B w s (t + 1) f := by
  intro k hk hk'
  rcases Nat.lt_or_ge k t with hlt | hge
  · exact h k hk hlt
  · have : k = t := by omega
    subst this
    exact hstep

omit [Fintype Q] in
/-- Extending a partial run by one step, using `Function.update` so that the values before
`t + 1` are not changed. -/
theorem exists_prun_succ {B : NBuchi Q Gam} {w : ℕ → Gam} {s t : ℕ} {f : ℕ → Q} {q : Q}
    (h : PRun B w s t f) (hstep : B.step (f t) (w t) q) :
    ∃ g : ℕ → Q, (∀ k, k ≤ t → g k = f k) ∧ g (t + 1) = q ∧ PRun B w s (t + 1) g := by
  classical
  refine ⟨Function.update f (t + 1) q, ?_, by simp, ?_⟩
  · intro k hk
    exact Function.update_of_ne (by omega) _ _
  · refine PRun.succ (fun k hk hk' => ?_) ?_
    · rw [Function.update_of_ne (show k ≠ t + 1 by omega),
        Function.update_of_ne (show k + 1 ≠ t + 1 by omega)]
      exact h k hk hk'
    · rw [Function.update_of_ne (show t ≠ t + 1 by omega), Function.update_self]
      exact hstep

/-! ### The label of the root -/

/-- The label of the root at time `n` is the set of the states reachable from the initial
states by a partial run of length `n`. -/
theorem mem_root_iff (B : NBuchi Q Gam) (w : ℕ → Gam) (n : ℕ) (q : Q) :
    q ∈ (treeRun B w n).lab [] ↔ ∃ f : ℕ → Q, f 0 ∈ B.start ∧ f n = q ∧ PRun B w 0 n f := by
  induction n generalizing q with
  | zero =>
      constructor
      · intro hq
        exact ⟨fun _ => q, hq, rfl, by intro k hk hk'; omega⟩
      · rintro ⟨f, hf0, hfn, -⟩
        rw [treeRun_zero, initTree_lab_nil, ← hfn]
        exact hf0
  | succ n ih =>
      rw [treeRun_succ, stepTree_lab_nil]
      constructor
      · rintro ⟨q0, hq0, hstep⟩
        obtain ⟨f, hf0, hfn, hrun⟩ := (ih q0).1 hq0
        obtain ⟨g, hg, hgn, hgrun⟩ := exists_prun_succ hrun (by rw [hfn]; exact hstep)
        exact ⟨g, by rw [hg 0 (Nat.zero_le _)]; exact hf0, hgn, hgrun⟩
      · rintro ⟨f, hf0, hfn, hrun⟩
        refine ⟨f n, (ih (f n)).2 ⟨f, hf0, rfl, hrun.mono (le_refl 0) (Nat.le_succ n)⟩, ?_⟩
        rw [← hfn]
        exact hrun n (Nat.zero_le _) (Nat.lt_succ_self n)

end Safra

end Lax369799Proofs.WordAutomata
