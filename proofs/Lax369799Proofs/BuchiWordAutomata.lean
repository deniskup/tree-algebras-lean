/-
Adapted from the Lean ancillary files of Bojańczyk, Casares, Manthe and
Parys, arXiv:2611.10136v1 (2026), with incorporation authorized by the user.
Original module: BorelMSO.Automata.MullerToBuchi.
Changes: Archive module paths and namespaces; port to the pinned toolchain.
See external-proofs.json for source provenance.
-/
import Lax369799Proofs.NondeterministicWordAutomata

/-!
# From nondeterministic Muller automata to nondeterministic Büchi automata

This file contains the first step of every standard proof of **McNaughton's determinization
theorem**: the reduction of the determinization of nondeterministic *Muller* automata on
ω-words to the determinization of nondeterministic *Büchi* automata, which is the step
carried out by Safra's construction.

A nondeterministic Büchi automaton (`Lax369799Proofs.WordAutomata.NBuchi`) accepts an ω-word if it has a run
visiting a distinguished set of states infinitely often.  Given a nondeterministic Muller
automaton `N`, the Büchi automaton `N.toBuchi` first follows a run of `N`, then guesses at
some point the set `F` of states that the run will visit infinitely often — the guess must
be accepting for `N` — and from then on it checks that the run stays inside `F` and visits
every state of `F` infinitely often, by means of the usual round-robin counter: the state
records the set of states of `F` that have not been visited yet in the current round, and
the round is restarted (and the state marked, which is the Büchi condition) whenever that
set becomes empty.

The main results are

* `Lax369799Proofs.WordAutomata.NMuller.accepts_toBuchi`: `N.toBuchi` accepts exactly the ω-words accepted
  by `N`;
* `Lax369799Proofs.WordAutomata.mcNaughton_of_buchiDeterminization`: McNaughton's theorem follows from the
  determinization of nondeterministic Büchi automata (`Lax369799Proofs.WordAutomata.BuchiDeterminization`,
  Safra's theorem).  Safra's theorem itself is proved in `Lax369799Proofs.WordAutomata/Safra/Main.lean`
  (`Lax369799Proofs.WordAutomata.buchiDeterminization`).
-/

namespace Lax369799Proofs.WordAutomata

/-- A nondeterministic Büchi automaton on ω-words. -/
structure NBuchi (S : Type*) (Gam : Type*) where
  /-- The set of initial states. -/
  start : Set S
  /-- The transition relation. -/
  step : S → Gam → S → Prop
  /-- The states that have to be visited infinitely often. -/
  fin : Set S

namespace NBuchi

variable {S Gam : Type*}

/-- A run of a nondeterministic Büchi automaton on an ω-word. -/
def IsRun (B : NBuchi S Gam) (w : ℕ → Gam) (r : ℕ → S) : Prop :=
  r 0 ∈ B.start ∧ ∀ n, B.step (r n) (w n) (r (n + 1))

/-- The automaton accepts the ω-word `w` if it has a run visiting `fin` infinitely often. -/
def Accepts (B : NBuchi S Gam) (w : ℕ → Gam) : Prop :=
  ∃ r, B.IsRun w r ∧ {n | r n ∈ B.fin}.Infinite

end NBuchi

/-- **Safra's determinization theorem**, as a statement.  It is proved in
`Lax369799Proofs.WordAutomata/Safra/Main.lean` (`Lax369799Proofs.WordAutomata.buchiDeterminization`).  Every language of ω-words recognized by a nondeterministic Büchi automaton with
finitely many states over a finite alphabet is recognized by a deterministic Muller
automaton. -/
def BuchiDeterminization : Prop :=
  ∀ (S Gam : Type) (_ : Finite S) (_ : Finite Gam) (B : NBuchi S Gam),
    ∃ (S' : Type) (_ : Finite S') (D : DMuller S' Gam), ∀ w, D.Accepts w ↔ B.Accepts w

namespace NMuller

variable {S Gam : Type} {N : NMuller S Gam}

/-- The states of the Büchi automaton associated with a Muller automaton: either a state of
the automaton (the guess has not been made yet), or a state together with the guessed set
`F`, the set of states of `F` that still have to be visited in the current round, and a flag
marking the end of a round. -/
abbrev BSt (S : Type) := S ⊕ (S × Set S × Set S × Bool)

/-- One step of the round-robin counter: the state `s` is removed from the set `X` of the
states that still have to be visited; when nothing else remains the round is over, the
counter is reset to `F` and the flag is raised. -/
def roundStep (F X : Set S) (s : S) (X' : Set S) (fl : Bool) : Prop :=
  ((∀ y ∈ X, y = s) ∧ X' = F ∧ fl = true) ∨
    ((¬ ∀ y ∈ X, y = s) ∧ X' = X \ {s} ∧ fl = false)

open Classical in
/-- The result of one step of the round-robin counter. -/
noncomputable def roundNext (F X : Set S) (s : S) : Set S × Bool :=
  if ∀ y ∈ X, y = s then (F, true) else (X \ {s}, false)

theorem roundStep_roundNext (F X : Set S) (s : S) :
    roundStep F X s (roundNext F X s).1 (roundNext F X s).2 := by
  classical
  unfold roundNext
  by_cases h : ∀ y ∈ X, y = s
  · rw [if_pos h]
    exact Or.inl ⟨h, rfl, rfl⟩
  · rw [if_neg h]
    exact Or.inr ⟨h, rfl, rfl⟩

/-- The Büchi automaton associated with a nondeterministic Muller automaton. -/
def toBuchi (N : NMuller S Gam) : NBuchi (BSt S) Gam where
  start := {q | ∃ s ∈ N.start, q = Sum.inl s}
  step q a q' :=
    match q, q' with
    | Sum.inl s, Sum.inl s' => N.step s a s'
    | Sum.inl s, Sum.inr (s', F, X', fl) =>
        N.step s a s' ∧ N.acc F ∧ s' ∈ F ∧ roundStep F F s' X' fl
    | Sum.inr (s, F, X, _), Sum.inr (s', F', X', fl) =>
        N.step s a s' ∧ N.acc F ∧ F' = F ∧ s' ∈ F ∧ roundStep F X s' X' fl
    | Sum.inr _, Sum.inl _ => False
  fin := {q | ∃ s F X, q = Sum.inr (s, F, X, true)}

/-- The state of the Muller automaton carried by a state of the Büchi automaton. -/
def proj : BSt S → S := Sum.elim id (fun p => p.1)

@[simp] theorem proj_inl (s : S) : proj (Sum.inl s) = s := rfl

@[simp] theorem proj_inr (p : S × Set S × Set S × Bool) : proj (Sum.inr p) = p.1 := rfl

theorem step_proj {q q' : BSt S} {a : Gam} (h : (toBuchi N).step q a q') :
    N.step (proj q) a (proj q') := by
  match q, q', h with
  | Sum.inl s, Sum.inl s', h => exact h
  | Sum.inl s, Sum.inr (s', F, X', fl), h => exact h.1
  | Sum.inr (s, F, X, b), Sum.inr (s', F', X', fl), h => exact h.1

/-! ### The Büchi automaton accepts at most as much as the Muller automaton -/

section Sound

variable {w : ℕ → Gam} {ρ : ℕ → BSt S}

/-- After the guess has been made, the guessed set no longer changes. -/
theorem stay_inr (hρ : (toBuchi N).IsRun w ρ) {n : ℕ} {s : S} {F X : Set S} {fl : Bool}
    (hn : ρ n = Sum.inr (s, F, X, fl)) :
    ∀ k, ∃ s' X' fl', ρ (n + k) = Sum.inr (s', F, X', fl') := by
  intro k
  induction k with
  | zero => exact ⟨s, X, fl, hn⟩
  | succ k ih =>
    obtain ⟨s', X', fl', hk⟩ := ih
    have hstep := hρ.2 (n + k)
    rw [hk] at hstep
    cases hnext : ρ (n + k + 1) with
    | inl s2 =>
      rw [hnext] at hstep
      exact (hstep : False).elim
    | inr p =>
      obtain ⟨s2, F2, X2, fl2⟩ := p
      rw [hnext] at hstep
      have hF : F2 = F := hstep.2.2.1
      exact ⟨s2, X2, fl2, by rw [hF]⟩

/-- Along the second phase, the states of the run belong to the guessed set. -/
theorem mem_of_inr (hρ : (toBuchi N).IsRun w ρ) {n : ℕ} {s : S} {F X : Set S} {fl : Bool}
    (hn : ρ (n + 1) = Sum.inr (s, F, X, fl)) : s ∈ F := by
  have hstep := hρ.2 n
  rw [hn] at hstep
  cases hprev : ρ n with
  | inl s0 =>
    rw [hprev] at hstep
    exact hstep.2.2.1
  | inr p =>
    obtain ⟨s0, F0, X0, fl0⟩ := p
    rw [hprev] at hstep
    have hF : F = F0 := hstep.2.2.1
    rw [hF]
    exact hstep.2.2.2.1

/-- The guessed set is accepting for the Muller automaton. -/
theorem acc_of_inr (hρ : (toBuchi N).IsRun w ρ) {n : ℕ} {s : S} {F X : Set S} {fl : Bool}
    (hn : ρ (n + 1) = Sum.inr (s, F, X, fl)) : N.acc F := by
  have hstep := hρ.2 n
  rw [hn] at hstep
  cases hprev : ρ n with
  | inl s0 =>
    rw [hprev] at hstep
    exact hstep.2.1
  | inr p =>
    obtain ⟨s0, F0, X0, fl0⟩ := p
    rw [hprev] at hstep
    have hF : F = F0 := hstep.2.2.1
    rw [hF]
    exact hstep.2.1

/-- A run of the Büchi automaton visiting `fin` infinitely often yields an accepting run of
the Muller automaton. -/
theorem accepts_of_toBuchi (h : (toBuchi N).Accepts w) : N.Accepts w := by
  classical
  obtain ⟨ρ, hρ, hinf⟩ := h
  refine ⟨fun n => proj (ρ n), ⟨?_, fun n => step_proj (hρ.2 n)⟩, ?_⟩
  · obtain ⟨s, hs, h0⟩ := hρ.1
    show proj (ρ 0) ∈ N.start
    rw [h0]
    exact hs
  -- a marked state is reached at some positive time
  obtain ⟨t1, ht1, ht1pos⟩ : ∃ t1, ρ t1 ∈ (toBuchi N).fin ∧ 1 ≤ t1 := by
    obtain ⟨t1, ht1, ht1ne⟩ := (hinf.diff (Set.finite_singleton 0)).nonempty
    exact ⟨t1, ht1, by
      rcases Nat.eq_zero_or_pos t1 with h | h
      · exact absurd (by simp [h]) ht1ne
      · exact h⟩
  obtain ⟨s0, F, X0, hF0⟩ := ht1
  obtain ⟨t0, rfl⟩ : ∃ t0, t1 = t0 + 1 := ⟨t1 - 1, by omega⟩
  have hacc : N.acc F := acc_of_inr hρ hF0
  have hstay := stay_inr hρ hF0
  choose sfun Xfun flfun hfun using hstay
  -- the data of the second phase
  have hround : ∀ k, roundStep F (Xfun k) (sfun (k + 1)) (Xfun (k + 1)) (flfun (k + 1)) := by
    intro k
    have hstep := hρ.2 (t0 + 1 + k)
    rw [hfun k, show t0 + 1 + k + 1 = t0 + 1 + (k + 1) from by ring, hfun (k + 1)] at hstep
    exact hstep.2.2.2.2
  have hmemF : ∀ k, sfun (k + 1) ∈ F := by
    intro k
    have hstep := hρ.2 (t0 + 1 + k)
    rw [hfun k, show t0 + 1 + k + 1 = t0 + 1 + (k + 1) from by ring, hfun (k + 1)] at hstep
    exact hstep.2.2.2.1
  have hsfun : ∀ k, proj (ρ (t0 + 1 + k)) = sfun k := by
    intro k
    rw [hfun k]
    rfl
  -- the set of states occurring infinitely often is exactly `F`
  have hsub : ∀ y, {n | proj (ρ n) = y}.Infinite → y ∈ F := by
    intro y hy
    have hy' : ∃ k, proj (ρ (t0 + 1 + (k + 1))) = y := by
      obtain ⟨n, hn, hn'⟩ := (hy.diff (Set.finite_Iic (t0 + 1))).nonempty
      simp only [Set.mem_Iic, not_le] at hn'
      exact ⟨n - (t0 + 2), by
        rw [show t0 + 1 + (n - (t0 + 2) + 1) = n from by omega]
        exact hn⟩
    obtain ⟨k, hk⟩ := hy'
    rw [hsfun (k + 1)] at hk
    rw [← hk]
    exact hmemF k
  -- every state of `F` occurs infinitely often
  have hresets : {k | flfun k = true}.Infinite := by
    have hsubset : {n | ρ n ∈ (toBuchi N).fin} ⊆
        (fun k => t0 + 1 + k) '' {k | flfun k = true} ∪ Set.Iic (t0 + 1) := by
      intro n hn
      by_cases hle : n ≤ t0 + 1
      · exact Or.inr hle
      · refine Or.inl ⟨n - (t0 + 1), ?_, show t0 + 1 + (n - (t0 + 1)) = n from by omega⟩
        have hkey := hfun (n - (t0 + 1))
        rw [show t0 + 1 + (n - (t0 + 1)) = n from by omega] at hkey
        obtain ⟨s', F', X', hfl⟩ := hn
        rw [hkey] at hfl
        simp only [Sum.inr.injEq, Prod.mk.injEq] at hfl
        exact hfl.2.2.2
    have := hinf.mono hsubset
    by_contra hfin
    rw [Set.not_infinite] at hfin
    exact this ((Set.Finite.image _ hfin).union (Set.finite_Iic _))
  have hvisit : ∀ k p, k ≤ p → Xfun k = F →
      ∀ y ∈ F, y ∈ Xfun p ∨ ∃ j, k < j ∧ j ≤ p ∧ sfun j = y := by
    intro k p hkp hk y hy
    induction p with
    | zero =>
      have : k = 0 := by omega
      subst this
      rw [hk]
      exact Or.inl hy
    | succ p ih =>
      rcases Nat.lt_or_ge k (p + 1) with hlt | hge
      · have hkp' : k ≤ p := by omega
        rcases ih hkp' with hmem | ⟨j, hj1, hj2, hj3⟩
        · rcases hround p with ⟨-, hX, -⟩ | ⟨-, hX, -⟩
          · rw [hX]
            exact Or.inl hy
          · by_cases hys : y = sfun (p + 1)
            · exact Or.inr ⟨p + 1, by omega, le_refl _, hys.symm⟩
            · refine Or.inl ?_
              rw [hX]
              exact ⟨hmem, by simpa using hys⟩
        · exact Or.inr ⟨j, hj1, by omega, hj3⟩
      · have : k = p + 1 := by omega
        subst this
        rw [hk]
        exact Or.inl hy
  have hXreset : ∀ k, flfun (k + 1) = true → Xfun (k + 1) = F ∧ ∀ z ∈ Xfun k, z = sfun (k + 1) := by
    intro k hk
    rcases hround k with ⟨h1, h2, -⟩ | ⟨-, -, h3⟩
    · exact ⟨h2, h1⟩
    · rw [h3] at hk
      exact absurd hk (by simp)
  have hsup : ∀ y ∈ F, {n | proj (ρ n) = y}.Infinite := by
    intro y hy
    refine Set.infinite_of_not_bddAbove ?_
    rintro ⟨M, hM⟩
    -- take two resets after `M`
    obtain ⟨k, hk, hkM⟩ : ∃ k, flfun k = true ∧ M + 1 ≤ k := by
      obtain ⟨k, hk, hk'⟩ := (hresets.diff (Set.finite_Iic (M + 1))).nonempty
      simp only [Set.mem_Iic, not_le] at hk'
      exact ⟨k, hk, by omega⟩
    obtain ⟨p, hp, hpk⟩ : ∃ p, flfun p = true ∧ k + 2 ≤ p := by
      obtain ⟨p, hp, hp'⟩ := (hresets.diff (Set.finite_Iic (k + 2))).nonempty
      simp only [Set.mem_Iic, not_le] at hp'
      exact ⟨p, hp, by omega⟩
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    obtain ⟨p', rfl⟩ : ∃ p', p = p' + 1 := ⟨p - 1, by omega⟩
    obtain ⟨hXk, -⟩ := hXreset k' hk
    obtain ⟨-, hlast⟩ := hXreset p' hp
    have hj : ∃ j, k' + 1 < j ∧ j ≤ p' + 1 ∧ sfun j = y := by
      rcases hvisit (k' + 1) p' (by omega) hXk y hy with hmem | ⟨j, hj1, hj2, hj3⟩
      · exact ⟨p' + 1, by omega, le_refl _, (hlast y hmem).symm⟩
      · exact ⟨j, hj1, by omega, hj3⟩
    obtain ⟨j, hj1, -, hj3⟩ := hj
    have : t0 + 1 + j ∈ {n | proj (ρ n) = y} := by
      simp only [Set.mem_setOf_eq, hsfun j, hj3]
    have := hM this
    omega
  have : NMuller.infStates (fun n => proj (ρ n)) = F := by
    ext y
    exact ⟨fun hy => hsub y hy, fun hy => hsup y hy⟩
  rw [this]
  exact hacc

end Sound


/-! ### The Büchi automaton accepts at least as much as the Muller automaton -/

section Complete

variable [Finite S] {w : ℕ → Gam}

/-- An accepting run of the Muller automaton yields an accepting run of the Büchi
automaton. -/
theorem toBuchi_accepts (h : N.Accepts w) : (toBuchi N).Accepts w := by
  classical
  obtain ⟨r, hrun, hacc⟩ := h
  set R := NMuller.infStates r with hR
  -- a time after which the run stays inside `R`
  obtain ⟨t0, ht0⟩ : ∃ t0, ∀ n, t0 ≤ n → r n ∈ R := by
    have hfin : {n | r n ∉ R}.Finite := by
      have hsplit : {n | r n ∉ R} = ⋃ y ∈ {y : S | y ∉ R}, {n | r n = y} := by
        ext n
        simp only [Set.mem_setOf_eq, Set.mem_iUnion, exists_prop]
        exact ⟨fun hn => ⟨r n, hn, rfl⟩, fun ⟨y, hy, hn⟩ => by rw [hn]; exact hy⟩
      rw [hsplit]
      refine Set.Finite.biUnion (Set.toFinite _) (fun y hy => ?_)
      simpa [hR, NMuller.infStates, Set.not_infinite] using hy
    obtain ⟨M, hM⟩ := hfin.bddAbove
    refine ⟨M + 1, fun n hn => ?_⟩
    by_contra hc
    have := hM (show n ∈ {n | r n ∉ R} from hc)
    omega
  -- the round-robin data
  obtain ⟨Z, hZ0, hZsucc⟩ : ∃ Z : ℕ → Set S × Bool, Z 0 = (R, true) ∧
      ∀ k, Z (k + 1) = roundNext R (Z k).1 (r (t0 + k + 1)) :=
    ⟨fun k => Nat.rec (R, true) (fun k p => roundNext R p.1 (r (t0 + k + 1))) k, rfl, fun _ => rfl⟩
  have hZsub : ∀ k, (Z k).1 ⊆ R := by
    intro k
    induction k with
    | zero => rw [hZ0]
    | succ k ih =>
      rw [hZsucc k]
      unfold roundNext
      by_cases hc : ∀ y ∈ (Z k).1, y = r (t0 + k + 1)
      · rw [if_pos hc]
      · rw [if_neg hc]
        exact fun y hy => ih hy.1
  -- infinitely many rounds are completed
  have hmarks : {k | (Z k).2 = true}.Infinite := by
    by_contra hfin
    rw [Set.not_infinite] at hfin
    obtain ⟨M, hM⟩ := hfin.bddAbove
    set K := M + 1 with hK
    have hfalse : ∀ k, K ≤ k → (Z k).2 = false := by
      intro k hk
      by_contra hc
      have : k ∈ {k | (Z k).2 = true} := by
        simp only [Set.mem_setOf_eq]
        cases hb : (Z k).2 with
        | false => exact absurd hb hc
        | true => rfl
      have := hM this
      omega
    have hstep : ∀ k, K ≤ k → (Z (k + 1)).1 = (Z k).1 \ {r (t0 + k + 1)} ∧
        ¬ (∀ y ∈ (Z k).1, y = r (t0 + k + 1)) := by
      intro k hk
      have hfl : (Z (k + 1)).2 = false := hfalse (k + 1) (by omega)
      by_cases hc : ∀ y ∈ (Z k).1, y = r (t0 + k + 1)
      · rw [hZsucc k] at hfl
        unfold roundNext at hfl
        rw [if_pos hc] at hfl
        exact absurd hfl (by simp)
      · refine ⟨?_, hc⟩
        rw [hZsucc k]
        unfold roundNext
        rw [if_neg hc]
    have hne : ∀ k, K ≤ k → (Z (k + 1)).1.Nonempty := by
      intro k hk
      obtain ⟨h1, h2⟩ := hstep k hk
      push_neg at h2
      obtain ⟨y, hy, hyne⟩ := h2
      exact ⟨y, by rw [h1]; exact ⟨hy, by simpa using hyne⟩⟩
    have hmono : ∀ j k, K ≤ j → j ≤ k → (Z k).1 ⊆ (Z j).1 := by
      intro j k hj hjk
      induction k with
      | zero =>
        have : j = 0 := by omega
        rw [this]
      | succ k ih =>
        rcases Nat.lt_or_ge j (k + 1) with hlt | hge
        · have hkj : j ≤ k := by omega
          refine subset_trans ?_ (ih hkj)
          rw [(hstep k (by omega)).1]
          exact fun y hy => hy.1
        · have : j = k + 1 := by omega
          rw [this]
    -- every element of the counter is eventually visited, so the counter empties
    have hchoice : ∀ y : S, ∃ j, K + 1 ≤ j ∧ (y ∈ (Z (K + 1)).1 → y ∉ (Z j).1) := by
      intro y
      by_cases hy : y ∈ (Z (K + 1)).1
      · have hyR : y ∈ R := hZsub (K + 1) hy
        have hinf : {n | r n = y}.Infinite := hyR
        obtain ⟨n, hn, hn'⟩ := (hinf.diff (Set.finite_Iic (t0 + K + 2))).nonempty
        simp only [Set.mem_Iic, not_le] at hn'
        refine ⟨n - t0, by omega, fun _ => ?_⟩
        have hk : n - t0 = (n - t0 - 1) + 1 := by omega
        rw [hk, (hstep (n - t0 - 1) (by omega)).1]
        simp only [Set.mem_diff, Set.mem_singleton_iff, not_and, not_not]
        intro _hmem
        rw [show t0 + (n - t0 - 1) + 1 = n from by omega]
        exact hn.symm
      · exact ⟨K + 1, le_refl _, fun hc => absurd hc hy⟩
    choose f hf1 hf2 using hchoice
    haveI : Fintype S := Fintype.ofFinite S
    set J := max (K + 1) (Finset.univ.sup f) with hJ
    have hJK : K + 1 ≤ J := le_max_left _ _
    have hempty : (Z J).1 = ∅ := by
      ext y
      simp only [Set.mem_empty_iff_false, iff_false]
      intro hy
      have hyK : y ∈ (Z (K + 1)).1 := hmono (K + 1) J (by omega) hJK hy
      have hfy : f y ≤ J := le_trans (Finset.le_sup (Finset.mem_univ y)) (le_max_right _ _)
      exact hf2 y hyK (hmono (f y) J (by have := hf1 y; omega) hfy hy)
    obtain ⟨j, hj⟩ : ∃ j, J = j + 1 := ⟨J - 1, by omega⟩
    obtain ⟨y, hy⟩ := hne j (by omega)
    rw [hj] at hempty
    rw [hempty] at hy
    exact hy
  -- the run of the Büchi automaton
  refine ⟨fun n => if n ≤ t0 then Sum.inl (r n)
    else Sum.inr (r n, R, (Z (n - t0)).1, (Z (n - t0)).2), ⟨?_, ?_⟩, ?_⟩
  · show (if (0 : ℕ) ≤ t0 then _ else _) ∈ _
    rw [if_pos (Nat.zero_le _)]
    exact ⟨r 0, hrun.1, rfl⟩
  · intro n
    rcases lt_trichotomy n t0 with hlt | heq | hgt
    · show (toBuchi N).step (if n ≤ t0 then _ else _) (w n) (if n + 1 ≤ t0 then _ else _)
      rw [if_pos (by omega : n ≤ t0), if_pos (by omega : n + 1 ≤ t0)]
      exact hrun.2 n
    · subst heq
      show (toBuchi N).step (if n ≤ n then _ else _) (w n) (if n + 1 ≤ n then _ else _)
      rw [if_pos (le_refl n), if_neg (by omega)]
      refine ⟨hrun.2 n, hacc, ht0 (n + 1) (by omega), ?_⟩
      have h1 : n + 1 - n = 1 := by omega
      rw [h1, hZsucc 0, hZ0]
      exact roundStep_roundNext R R (r (n + 0 + 1))
    · show (toBuchi N).step (if n ≤ t0 then _ else _) (w n) (if n + 1 ≤ t0 then _ else _)
      rw [if_neg (by omega), if_neg (by omega)]
      refine ⟨hrun.2 n, hacc, rfl, ht0 (n + 1) (by omega), ?_⟩
      have h1 : n + 1 - t0 = (n - t0) + 1 := by omega
      rw [h1, hZsucc (n - t0), show t0 + (n - t0) + 1 = n + 1 from by omega]
      exact roundStep_roundNext R (Z (n - t0)).1 (r (n + 1))
  · have himg : (fun k => t0 + k) '' {k | 1 ≤ k ∧ (Z k).2 = true} ⊆
        {n | (if n ≤ t0 then Sum.inl (r n)
          else Sum.inr (r n, R, (Z (n - t0)).1, (Z (n - t0)).2)) ∈ (toBuchi N).fin} := by
      rintro n ⟨k, ⟨hk1, hk2⟩, rfl⟩
      simp only [Set.mem_setOf_eq]
      rw [if_neg (show ¬ (t0 + k ≤ t0) by omega), show t0 + k - t0 = k from by omega]
      exact ⟨r (t0 + k), R, (Z k).1, by rw [hk2]⟩
    refine Set.Infinite.mono himg (Set.Infinite.image ?_ ?_)
    · exact fun a _ b _ hab => by omega
    · have : {k | 1 ≤ k ∧ (Z k).2 = true} = {k | (Z k).2 = true} \ {0} := by
        ext k
        simp only [Set.mem_setOf_eq, Set.mem_diff, Set.mem_singleton_iff]
        constructor
        · rintro ⟨h1, h2⟩
          exact ⟨h2, by omega⟩
        · rintro ⟨h1, h2⟩
          exact ⟨by omega, h1⟩
      rw [this]
      exact hmarks.diff (Set.finite_singleton 0)

end Complete

/-- The Büchi automaton associated with a nondeterministic Muller automaton recognizes the
same language. -/
theorem accepts_toBuchi [Finite S] (w : ℕ → Gam) : (toBuchi N).Accepts w ↔ N.Accepts w :=
  ⟨accepts_of_toBuchi, toBuchi_accepts⟩

end NMuller

/-- **McNaughton's theorem follows from Safra's determinization of nondeterministic Büchi
automata.**  Every nondeterministic Muller automaton on ω-words is turned into an equivalent
nondeterministic Büchi automaton, which is then determinized. -/
theorem mcNaughton_of_buchiDeterminization (h : BuchiDeterminization) : McNaughton := by
  intro S Gam hS hGam N
  obtain ⟨S', hS', D, hD⟩ := h (NMuller.BSt S) Gam inferInstance inferInstance (N.toBuchi)
  exact ⟨S', hS', D, fun w => (hD w).trans (N.accepts_toBuchi w)⟩

end Lax369799Proofs.WordAutomata
