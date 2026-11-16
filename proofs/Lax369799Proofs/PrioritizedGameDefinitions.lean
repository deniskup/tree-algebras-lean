/-
Adapted from the Lean ancillary files of Bojańczyk, Casares, Manthe and
Parys, arXiv:2611.10136v1 (2026), with incorporation authorized by the user.
Original module: BorelMSO.Basic.Prioritized.
Changes: Archive module paths and namespaces; port to the pinned toolchain.
See external-proofs.json for source provenance.
-/
import Mathlib.Algebra.Group.Nat.Even
import Mathlib.Data.Set.Finite.Lattice

/-! Recurring priorities of an infinite sequence. -/

namespace Lax369799Proofs.WordAutomata

/-- The value `i` occurs infinitely often in the sequence `f`. -/
def InfOften (f : ℕ → ℕ) (i : ℕ) : Prop := ∀ N, ∃ n, N ≤ n ∧ f n = i

/-- `i` is the maximal value occurring infinitely often in `f`. -/
def MaxInfOften (f : ℕ → ℕ) (i : ℕ) : Prop :=
  InfOften f i ∧ ∀ j, i < j → ¬ InfOften f j

theorem MaxInfOften.unique {f : ℕ → ℕ} {i j : ℕ} (hi : MaxInfOften f i)
    (hj : MaxInfOften f j) : i = j := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with h | h
  · exact hi.2 j h hj.1
  · exact hj.2 i h hi.1

end Lax369799Proofs.WordAutomata
