/-
Adapted from the Lean ancillary files of Bojańczyk, Casares, Manthe and
Parys, arXiv:2611.10136v1 (2026), with incorporation authorized by the user.
Original module: BorelMSO.Automata.DetMuller.
Changes: Archive module paths and namespaces; port to the pinned toolchain.
See external-proofs.json for source provenance.
-/
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Finite.Prod
import Mathlib.Data.Finite.Sum
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Data.Set.Finite.Lattice
import Mathlib.Tactic.Convert
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Push
import Mathlib.Tactic.Choose

/-! Finite deterministic Muller word automata and their runs. -/

namespace Lax369799Proofs.WordAutomata

/-- A deterministic Muller automaton on ω-words: a deterministic transition function
together with an acceptance condition given by a family of sets of states. -/
structure DMuller (S : Type*) (Gam : Type*) where
  /-- The initial state. -/
  start : S
  /-- The (deterministic) transition function. -/
  step : S → Gam → S
  /-- The accepting family: the sets of states which are allowed to occur infinitely
  often. -/
  acc : Set S → Prop

namespace DMuller

variable {S Gam : Type*}

/-- The run of a deterministic automaton on an ω-word. -/
def run (M : DMuller S Gam) (w : ℕ → Gam) : ℕ → S
  | 0 => M.start
  | n + 1 => M.step (M.run w n) (w n)

@[simp] theorem run_zero (M : DMuller S Gam) (w : ℕ → Gam) : M.run w 0 = M.start := rfl

@[simp] theorem run_succ (M : DMuller S Gam) (w : ℕ → Gam) (n : ℕ) :
    M.run w (n + 1) = M.step (M.run w n) (w n) := rfl

/-- The set of states occurring infinitely often in the run of `M` on `w`. -/
def infStates (M : DMuller S Gam) (w : ℕ → Gam) : Set S :=
  {s | {n | M.run w n = s}.Infinite}

/-- The automaton accepts the ω-word `w`. -/
def Accepts (M : DMuller S Gam) (w : ℕ → Gam) : Prop := M.acc (M.infStates w)

/-! ### The tree automaton of Claim 14 -/

end DMuller

end Lax369799Proofs.WordAutomata
