/-
Adapted from the Lean ancillary files of Bojańczyk, Casares, Manthe and
Parys, arXiv:2611.10136v1 (2026), with incorporation authorized by the user.
Original module: BorelMSO.Automata.OmegaAut.
Changes: Archive module paths and namespaces; port to the pinned toolchain.
See external-proofs.json for source provenance.
-/
import Lax369799Proofs.MullerWordAutomata

/-!
# Nondeterministic Muller automata on ω-words and determinization

The proof of Claim 14 (`Lax369799Proofs.WordAutomata/Automata/DetMuller.lean`) needs, for each letter of the
alphabet, a *deterministic* Muller automaton on ω-words.  The properties of the branches
that have to be checked in the proof of Lemma 12 are naturally described by
*nondeterministic* automata, and moreover they are the *complements* of such properties.

Passing from a nondeterministic Muller automaton to an equivalent deterministic one is
McNaughton's determinization theorem.  It is not available in Mathlib.  It is stated here as
the predicate `Lax369799Proofs.WordAutomata.McNaughton`, so that the results needing it can take it as a
hypothesis.  The predicate is proved later, in `Lax369799Proofs.WordAutomata/Safra/Main.lean`
(`Lax369799Proofs.WordAutomata.mcNaughton`, via Safra's construction), and the final results, such as Lemma 12
(`Lax369799Proofs.WordAutomata.Automaton.lemma12`), do not assume it.

Once an automaton is deterministic, complementing it is immediate: it suffices to complement
its acceptance condition (`Lax369799Proofs.WordAutomata.DMuller.compl`).
-/

namespace Lax369799Proofs.WordAutomata

/-- A nondeterministic Muller automaton on ω-words. -/
structure NMuller (S : Type*) (Gam : Type*) where
  /-- The set of initial states. -/
  start : Set S
  /-- The transition relation. -/
  step : S → Gam → S → Prop
  /-- The accepting family: the sets of states which are allowed to occur infinitely
  often. -/
  acc : Set S → Prop

namespace NMuller

variable {S Gam : Type*}

/-- A run of a nondeterministic automaton on an ω-word. -/
def IsRun (N : NMuller S Gam) (w : ℕ → Gam) (r : ℕ → S) : Prop :=
  r 0 ∈ N.start ∧ ∀ n, N.step (r n) (w n) (r (n + 1))

/-- The set of states occurring infinitely often in a run. -/
def infStates (r : ℕ → S) : Set S := {s | {n | r n = s}.Infinite}

/-- The automaton accepts the ω-word `w` if it has an accepting run on `w`. -/
def Accepts (N : NMuller S Gam) (w : ℕ → Gam) : Prop :=
  ∃ r, N.IsRun w r ∧ N.acc (infStates r)

end NMuller

namespace DMuller

variable {S Gam : Type*}

/-- The complement of a deterministic Muller automaton: the acceptance condition is
negated. -/
def compl (M : DMuller S Gam) : DMuller S Gam :=
  { M with acc := fun R => ¬ M.acc R }

@[simp] theorem run_compl (M : DMuller S Gam) (w : ℕ → Gam) (n : ℕ) :
    M.compl.run w n = M.run w n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      show M.step (M.compl.run w n) (w n) = M.step (M.run w n) (w n)
      rw [ih]

@[simp] theorem accepts_compl (M : DMuller S Gam) (w : ℕ → Gam) :
    M.compl.Accepts w ↔ ¬ M.Accepts w := by
  simp only [Accepts, infStates, run_compl]
  rfl

end DMuller

/-- **McNaughton's determinization theorem** (stated as a proposition; it is proved in `Lax369799Proofs.WordAutomata/Safra/Main.lean`).  Every language of
ω-words recognized by a nondeterministic Muller automaton with finitely many states over a
finite alphabet is recognized by a deterministic Muller automaton. -/
def McNaughton : Prop :=
  ∀ (S Gam : Type) (_ : Finite S) (_ : Finite Gam) (N : NMuller S Gam),
    ∃ (S' : Type) (_ : Finite S') (D : DMuller S' Gam), ∀ w, D.Accepts w ↔ N.Accepts w

/-- Assuming McNaughton's theorem, the complement of the language of a nondeterministic
Muller automaton is recognized by a deterministic Muller automaton. -/
theorem exists_dmuller_compl (h : McNaughton) {S Gam : Type} [Finite S] [Finite Gam]
    (N : NMuller S Gam) :
    ∃ (S' : Type) (_ : Finite S') (D : DMuller S' Gam), ∀ w, D.Accepts w ↔ ¬ N.Accepts w := by
  obtain ⟨S', hS', D, hD⟩ := h S Gam inferInstance inferInstance N
  exact ⟨S', hS', D.compl, fun w => by rw [DMuller.accepts_compl, hD]⟩

end Lax369799Proofs.WordAutomata
