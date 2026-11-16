/-
Adapted from the Lean ancillary files of Bojańczyk, Casares, Manthe and
Parys, arXiv:2611.10136v1 (2026), with incorporation authorized by the user.
Original module: BorelMSO.Basic.Konig.
Changes: Archive module paths and namespaces; port to the pinned toolchain.
See external-proofs.json for source provenance.
-/
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Finset.Lattice.Fold

/-!
# A König-type lemma for ω-indexed systems of finite sets

This file contains an auxiliary compactness result used in the formalization of
games on tree-like arenas: if `S 0, S 1, S 2, …` are nonempty finite sets and `r`
maps `S (n+1)` into `S n`, then there is a coherent sequence `c n ∈ S n` with
`r (c (n+1)) = c n`.
-/

namespace Lax369799Proofs.WordAutomata

variable {X : Type*}

/-- `Ext S r n x` says that `x` can be extended to arbitrarily high levels of the system:
for every `m` there is an element `y` of `S (n + m)` restricting to `x`. -/
def Ext (S : ℕ → Set X) (r : X → X) (n : ℕ) (x : X) : Prop :=
  ∀ m, ∃ y ∈ S (n + m), r^[m] y = x

theorem mem_of_ext {S : ℕ → Set X} {r : X → X} {n : ℕ} {x : X} (h : Ext S r n x) :
    x ∈ S n := by
  obtain ⟨y, hy, hxy⟩ := h 0
  simpa [← hxy] using hy

theorem iterate_mem {S : ℕ → Set X} {r : X → X}
    (hr : ∀ n, ∀ x ∈ S (n + 1), r x ∈ S n) :
    ∀ (j n : ℕ) (x : X), x ∈ S (n + j) → r^[j] x ∈ S n := by
  intro j
  induction j with
  | zero => intro n x hx; simpa using hx
  | succ j ih =>
    intro n x hx
    rw [Function.iterate_succ_apply]
    refine ih n (r x) (hr (n + j) x ?_)
    rw [show n + j + 1 = n + (j + 1) from rfl]
    exact hx

/-- Every level contains an element that extends arbitrarily far. -/
theorem exists_ext {S : ℕ → Set X} {r : X → X}
    (hne : ∀ n, (S n).Nonempty) (hfin : ∀ n, (S n).Finite)
    (hr : ∀ n, ∀ x ∈ S (n + 1), r x ∈ S n) (n : ℕ) :
    ∃ x, Ext S r n x := by
  classical
  by_contra hcon
  push_neg at hcon
  have h : ∀ x : X, ∃ m, ∀ y ∈ S (n + m), r^[m] y ≠ x := by
    intro x
    have hx := hcon x
    unfold Ext at hx
    push_neg at hx
    exact hx
  choose m hm using h
  set M := (hfin n).toFinset.sup m with hM
  obtain ⟨z, hz⟩ := hne (n + M)
  have hx : r^[M] z ∈ S n := iterate_mem hr M n z hz
  have hmM : m (r^[M] z) ≤ M := by
    rw [hM]
    exact Finset.le_sup (by simpa using hx)
  have hz' : r^[M - m (r^[M] z)] z ∈ S (n + m (r^[M] z)) := by
    apply iterate_mem hr
    have : n + M = n + m (r^[M] z) + (M - m (r^[M] z)) := by omega
    rw [← this]; exact hz
  refine hm _ _ hz' ?_
  rw [← Function.iterate_add_apply]
  congr 1
  omega

/-- An element that extends arbitrarily far has a successor that extends arbitrarily far. -/
theorem exists_ext_succ {S : ℕ → Set X} {r : X → X}
    (hfin : ∀ n, (S n).Finite) (hr : ∀ n, ∀ x ∈ S (n + 1), r x ∈ S n)
    (n : ℕ) (x : X) (hx : Ext S r n x) :
    ∃ y, r y = x ∧ Ext S r (n + 1) y := by
  classical
  by_contra hcon
  push_neg at hcon
  have h : ∀ y : X, r y = x → ∃ m, ∀ z ∈ S (n + 1 + m), r^[m] z ≠ y := by
    intro y hy
    have hny := hcon y hy
    unfold Ext at hny
    push_neg at hny
    exact hny
  choose! m hm using h
  set M := (hfin (n + 1)).toFinset.sup m with hM
  obtain ⟨z, hz, hzx⟩ := hx (M + 1)
  have hz1 : r^[M] z ∈ S (n + 1) := by
    apply iterate_mem hr
    have : n + (M + 1) = n + 1 + M := by omega
    rw [← this]; exact hz
  have hrz : r (r^[M] z) = x := by
    rw [← Function.iterate_succ_apply' r M z]
    exact hzx
  have hmM : m (r^[M] z) ≤ M := by
    rw [hM]
    exact Finset.le_sup (by simpa using hz1)
  have hz' : r^[M - m (r^[M] z)] z ∈ S (n + 1 + m (r^[M] z)) := by
    apply iterate_mem hr
    have : n + (M + 1) = n + 1 + m (r^[M] z) + (M - m (r^[M] z)) := by omega
    rw [← this]; exact hz
  refine hm _ hrz _ hz' ?_
  rw [← Function.iterate_add_apply]
  congr 1
  omega

/-- **König's lemma** for an ω-indexed inverse system of nonempty finite sets. -/
theorem exists_coherent_seq (S : ℕ → Set X) (r : X → X)
    (hne : ∀ n, (S n).Nonempty) (hfin : ∀ n, (S n).Finite)
    (hr : ∀ n, ∀ x ∈ S (n + 1), r x ∈ S n) :
    ∃ c : ℕ → X, (∀ n, c n ∈ S n) ∧ ∀ n, r (c (n + 1)) = c n := by
  classical
  obtain ⟨x0, hx0⟩ := exists_ext hne hfin hr 0
  choose f hf1 hf2 using exists_ext_succ hfin hr
  let c : ∀ n, {x // Ext S r n x} := fun n =>
    Nat.rec (motive := fun n => {x // Ext S r n x}) ⟨x0, hx0⟩
      (fun n p => ⟨f n p.1 p.2, hf2 n p.1 p.2⟩) n
  refine ⟨fun n => (c n).1, fun n => mem_of_ext (c n).2, fun n => ?_⟩
  exact hf1 n (c n).1 (c n).2

end Lax369799Proofs.WordAutomata
