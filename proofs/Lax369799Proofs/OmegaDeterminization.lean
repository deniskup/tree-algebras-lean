import Lax369799.OmegaDeterminization
import Lax369799Proofs.SafraDeterminization
import Lax369799Proofs.AppearanceSequences

namespace Lax369799Proofs.OmegaDeterminization
set_option backward.isDefEq.respectTransparency false
open Lax369799.UnfoldAutomata Lax369799.OmegaDeterminization
open WordAutomata
open scoped Classical

private theorem reverse_parity {f : ℕ → ℕ} {B : ℕ}
    (hB : Even B) (hbound : ∀ n, f n ≤ B) :
    (∃ p, MaxInfOften f p ∧ Even p) ↔
    ∃ c, Even c ∧ (∀ N, ∃ n, N ≤ n ∧ B - f n = c) ∧
      ∀ b, b < c → ∃ N, ∀ n, N ≤ n → B - f n ≠ b := by
  classical
  constructor
  · rintro ⟨p, ⟨hp, hmax⟩, heven⟩
    have hpB : p ≤ B := by
      obtain ⟨n, -, hn⟩ := hp 0
      simpa only [hn] using hbound n
    refine ⟨B - p, (Nat.even_sub hpB).2 (by simp [hB, heven]), ?_, ?_⟩
    · intro N
      obtain ⟨n, hn, hn'⟩ := hp N
      exact ⟨n, hn, by rw [hn']⟩
    · intro b hb
      have hninf := hmax (B - b) (by omega)
      simp only [InfOften, not_forall, not_exists, not_and] at hninf
      obtain ⟨N, hN⟩ := hninf
      exact ⟨N, fun n hn hc => hN n hn (by have := hbound n; omega)⟩
  · rintro ⟨c, heven, hc, hmin⟩
    have hcB : c ≤ B := by
      obtain ⟨n, -, hn⟩ := hc 0
      omega
    refine ⟨B - c, ⟨?_, ?_⟩, (Nat.even_sub hcB).2 (by simp [hB, heven])⟩
    · intro N
      obtain ⟨n, hn, heq⟩ := hc N
      exact ⟨n, hn, by have := hbound n; omega⟩
    · intro j hj hji
      obtain ⟨n, -, hn⟩ := hji 0
      have hjB : j ≤ B := by simpa only [hn] using hbound n
      obtain ⟨N, hN⟩ := hmin (B - j) (by omega)
      obtain ⟨n, hn, heq⟩ := hji N
      exact hN n hn (by rw [heq])

noncomputable def parity {S : Type} [Fintype S]
    {u z : ℕ} (M : DMuller S (Fin u)) : WordCondition u z := by
  classical
  letI : Nonempty S := ⟨M.start⟩
  let Q := S × (S → Fin (Fintype.card S))
  let e := Fintype.equivFin Q
  exact {
    states := Fintype.card Q
    initial := e (M.start, Fintype.equivFin S)
    step := fun q a => match a with
      | .inl b => e (M.step (e.symm q).1 b,
          LAR.upd (e.symm q).1 (e.symm q).2)
      | .inr _ => q
    priority := fun q => 2 * Fintype.card S -
      LARSeq.prioOf {R | M.acc R} (e.symm q).1 (e.symm q).2
    final := ∅ }

private theorem parity_run {S : Type} [Fintype S] [Nonempty S]
    {u z : ℕ} (M : DMuller S (Fin u)) (w : ℕ → Fin u) (n : ℕ) :
    (Fintype.equivFin (S × (S → Fin (Fintype.card S)))).symm
      ((parity (z := z) M).run w n) =
      (M.run w n, LARSeq.recSeq (M.run w) (Fintype.equivFin S) n) := by
  classical
  induction n with
  | zero => simp [WordCondition.run, parity, DMuller.run, LARSeq.recSeq]
  | succ n ih =>
    let e := Fintype.equivFin (S × (S → Fin (Fintype.card S)))
    change e.symm (e (M.step (e.symm ((parity M).run w n)).1 (w n),
      LAR.upd (e.symm ((parity M).run w n)).1
        (e.symm ((parity M).run w n)).2)) = _
    rw [e.symm_apply_apply, ih]
    rfl

theorem parity_correct {S : Type} [Fintype S]
    {u z : ℕ} (M : DMuller S (Fin u)) (w : ℕ → Fin u) :
    (parity (z := z) M).AcceptsInfinite w ↔ M.Accepts w := by
  classical
  letI : Nonempty S := ⟨M.start⟩
  let r0 := Fintype.equivFin S
  let f := fun n => LARSeq.prioOf {R | M.acc R} (M.run w n)
    (LARSeq.recSeq (M.run w) r0 n)
  have hbound (n : ℕ) : f n ≤ 2 * Fintype.card S := by
    have hlt := (LARSeq.recSeq (M.run w) r0 n (M.run w n)).isLt
    dsimp only [LAR.card] at hlt
    dsimp only [f, LARSeq.prioOf]
    split <;> omega
  have hprio (n : ℕ) : (parity (z := z) M).priority ((parity M).run w n) =
      2 * Fintype.card S - f n := by
    change 2 * Fintype.card S - LARSeq.prioOf _ _ _ = _
    rw [parity_run (z := z) M w n]
  simp only [WordCondition.AcceptsInfinite, hprio]
  rw [← reverse_parity (even_two_mul _) hbound]
  exact LARSeq.exists_even_maxInfOften_iff {R | M.acc R} (M.run w)
    (Fintype.equivFin S).injective

/--
---
conclusion: Lax369799.OmegaDeterminization.determinization
---
Safra's construction gives a deterministic Muller automaton. Latest
appearance records convert its condition to parity; reversal around an
even bound gives the least-priority convention used for branches.
The Safra and appearance-record proofs are adapted from the ancillary
Lean development of Bojańczyk, Casares, Manthe and Parys (2026).
-/
theorem determinization {u z : ℕ} (B : Buchi u) :
    ∃ D : WordCondition u z, ∀ w, D.AcceptsInfinite w ↔ B.Accepts w := by
  let N : NBuchi (Fin B.states) (Fin u) := {
    start := B.initial, step := B.transition, fin := B.accepting }
  obtain ⟨S, hS, M, hM⟩ := buchiDeterminization (Fin B.states) (Fin u)
    inferInstance inferInstance N
  letI : Finite S := hS
  letI : Fintype S := Fintype.ofFinite S
  refine ⟨parity M, fun w => (parity_correct M w).trans ((hM w).trans ?_)⟩
  change (∃ r : ℕ → Fin B.states, (r 0 ∈ B.initial ∧ ∀ n, B.transition (r n) (w n) (r (n + 1))) ∧
    {n | r n ∈ B.accepting}.Infinite) ↔ _
  simp only [Buchi.Accepts, and_assoc]

end Lax369799Proofs.OmegaDeterminization
