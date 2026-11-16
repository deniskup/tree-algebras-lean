/-
Adapted from the Lean ancillary files of Bojańczyk, Casares, Manthe and
Parys, arXiv:2611.10136v1 (2026), with incorporation authorized by the user.
Original module: BorelMSO.Emptiness.FinGame.
Changes: Archive module paths and namespaces; port to the pinned toolchain.
See external-proofs.json for source provenance.
-/
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Data.Finset.Max
import Mathlib.Algebra.Group.Nat.Even
import Mathlib.Data.Set.Finite.Lattice
import Lax369799Proofs.PrioritizedGameDefinitions

/-!
# Games on finite arenas with a parity condition

This file sets up the basic vocabulary of two-player games on a *finite* arena, which is
what is needed to decide emptiness of Muller tree automata (Lemma 7 of the paper).

An arena is a set of vertices `V`, an ownership predicate `own` (the vertices of Eve), an
edge relation `E` and a priority function `prio`.  Since we are going to prove *positional*
determinacy, all strategies considered here are positional: a strategy is simply a function
`V → V`.  Plays are infinite paths `π : ℕ → V`; Eve wins a play if the maximal priority
occurring infinitely often is even.

Everything is relativized to a subset `S : Set V` of the vertices, which plays the role of a
subgame: `Closed a S` says that every vertex of `S` has a successor in `S`, and plays are
required to stay inside `S`.  This avoids having to build a new arena on a subtype when
restricting the game, which is what happens repeatedly in Zielonka's induction.

The last section defines the *dual* arena (swap the owners and shift the priorities by one),
which exchanges the roles of the two players and lets us prove only "Eve's half" of each
statement.
-/

namespace Lax369799Proofs.WordAutomata

namespace FinGame

/-! ### Infinitely often -/

theorem infOften_shift {f : ℕ → ℕ} {i m : ℕ} :
    InfOften (fun n => f (n + m)) i ↔ InfOften f i := by
  constructor
  · intro h N
    obtain ⟨n, hn, hfn⟩ := h N
    exact ⟨n + m, by omega, hfn⟩
  · intro h N
    obtain ⟨n, hn, hfn⟩ := h (N + m)
    refine ⟨n - m, by omega, ?_⟩
    have hnm : n - m + m = n := by omega
    show f (n - m + m) = i
    rw [hnm]
    exact hfn

theorem maxInfOften_shift {f : ℕ → ℕ} {i m : ℕ} :
    MaxInfOften (fun n => f (n + m)) i ↔ MaxInfOften f i := by
  simp only [MaxInfOften]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨infOften_shift.1 h1, fun j hj hc => h2 j hj (infOften_shift.2 hc)⟩
  · rintro ⟨h1, h2⟩
    exact ⟨infOften_shift.2 h1, fun j hj hc => h2 j hj (infOften_shift.1 hc)⟩

/-- Some value occurs infinitely often in a bounded sequence of naturals. -/
theorem exists_infOften {f : ℕ → ℕ} {B : ℕ} (hB : ∀ n, f n ≤ B) : ∃ i, InfOften f i := by
  by_contra hcon
  push_neg at hcon
  have hfin : ∀ i, {n | f n = i}.Finite := by
    intro i
    have hci : ¬ InfOften f i := hcon i
    simp only [InfOften, not_forall, not_exists, not_and] at hci
    obtain ⟨N, hN⟩ := hci
    apply Set.Finite.subset (Set.finite_Iio N)
    intro n hn
    simp only [Set.mem_setOf_eq] at hn
    by_contra hcon2
    exact (hN n (by simpa using hcon2)) hn
  have huniv : (Set.univ : Set ℕ) ⊆ ⋃ i ∈ Set.Iic B, {n | f n = i} := by
    intro n _
    exact Set.mem_biUnion (hB n) rfl
  exact Set.infinite_univ (Set.Finite.subset
    ((Set.finite_Iic B).biUnion (fun i _ => hfin i)) huniv)

/-- A bounded sequence of naturals has a maximal value occurring infinitely often. -/
theorem exists_maxInfOften {f : ℕ → ℕ} {B : ℕ} (hB : ∀ n, f n ≤ B) :
    ∃ i, MaxInfOften f i := by
  classical
  have hsub : {i | InfOften f i} ⊆ Set.Iic B := by
    intro i hi
    obtain ⟨n, -, hn⟩ := hi 0
    exact hn ▸ hB n
  have hfin : {i | InfOften f i}.Finite := Set.Finite.subset (Set.finite_Iic B) hsub
  obtain ⟨i, hi⟩ := exists_infOften hB
  have hne : hfin.toFinset.Nonempty := ⟨i, by simpa using hi⟩
  refine ⟨hfin.toFinset.max' hne, ?_, fun j hj hjinf => ?_⟩
  · have := hfin.toFinset.max'_mem hne
    simpa using this
  · have hle : j ≤ hfin.toFinset.max' hne :=
      hfin.toFinset.le_max' j (by simpa using hjinf)
    omega

theorem maxInfOften_of_le {f : ℕ → ℕ} {p : ℕ} (hle : ∀ n, f n ≤ p) (hp : InfOften f p) :
    MaxInfOften f p := by
  refine ⟨hp, fun j hj hjinf => ?_⟩
  obtain ⟨n, -, hn⟩ := hjinf 0
  have := hle n
  omega

theorem maxInfOften_succ {f : ℕ → ℕ} {i : ℕ} :
    MaxInfOften (fun n => f n + 1) (i + 1) ↔ MaxInfOften f i := by
  have hio : ∀ j, InfOften (fun n => f n + 1) (j + 1) ↔ InfOften f j := by
    intro j
    constructor
    · intro h N
      obtain ⟨n, hn, hfn⟩ := h N
      have hfn' : f n + 1 = j + 1 := hfn
      exact ⟨n, hn, by omega⟩
    · intro h N
      obtain ⟨n, hn, hfn⟩ := h N
      exact ⟨n, hn, by simp [hfn]⟩
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨(hio i).1 h1, fun j hj hjinf => h2 (j + 1) (by omega) ((hio j).2 hjinf)⟩
  · rintro ⟨h1, h2⟩
    refine ⟨(hio i).2 h1, fun j hj hjinf => ?_⟩
    obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
    exact h2 j' (by omega) ((hio j').1 hjinf)

/-! ### Arenas -/

/-- A finite arena with a parity condition: `own v` says that the vertex `v` belongs to Eve,
`E` is the edge relation and `prio` the priority function. -/
structure Arena (V : Type) where
  /-- The vertices owned by Eve. -/
  own : V → Prop
  /-- The edge relation. -/
  E : V → V → Prop
  /-- The priority of a vertex. -/
  prio : V → ℕ

namespace Arena

variable {V : Type} (a : Arena V)

/-- An infinite path in the arena. -/
def IsPath (π : ℕ → V) : Prop := ∀ n, a.E (π n) (π (n + 1))

/-- An infinite path staying inside the set `S`. -/
def PathIn (S : Set V) (π : ℕ → V) : Prop := a.IsPath π ∧ ∀ n, π n ∈ S

/-- Every vertex of `S` has a successor inside `S`. -/
def Closed (S : Set V) : Prop := ∀ v ∈ S, ∃ w ∈ S, a.E v w

/-- The sequence of priorities along a play. -/
def prioSeq (π : ℕ → V) : ℕ → ℕ := fun n => a.prio (π n)

/-- Eve wins a play if the maximal priority occurring infinitely often is even. -/
def EveWinsPlay (π : ℕ → V) : Prop := ∃ p, MaxInfOften (a.prioSeq π) p ∧ Even p

/-- A positional strategy of Eve is legal in `S`. -/
def EveOK (S : Set V) (f : V → V) : Prop := ∀ v ∈ S, a.own v → f v ∈ S ∧ a.E v (f v)

/-- A positional strategy of Adam is legal in `S`. -/
def AdamOK (S : Set V) (g : V → V) : Prop := ∀ v ∈ S, ¬ a.own v → g v ∈ S ∧ a.E v (g v)

/-- The play is consistent with Eve's positional strategy `f`. -/
def ConsE (f : V → V) (π : ℕ → V) : Prop := ∀ n, a.own (π n) → π (n + 1) = f (π n)

/-- The play is consistent with Adam's positional strategy `g`. -/
def ConsA (g : V → V) (π : ℕ → V) : Prop := ∀ n, ¬ a.own (π n) → π (n + 1) = g (π n)

/-- Eve's strategy `f` wins from `v` inside `S`. -/
def WinsE (S : Set V) (f : V → V) (v : V) : Prop :=
  ∀ π, a.PathIn S π → π 0 = v → a.ConsE f π → a.EveWinsPlay π

/-- Adam's strategy `g` wins from `v` inside `S`. -/
def WinsA (S : Set V) (g : V → V) (v : V) : Prop :=
  ∀ π, a.PathIn S π → π 0 = v → a.ConsA g π → ¬ a.EveWinsPlay π

/-! ### Basic facts about plays -/

/-- Shifting a play in time. -/
def shift (π : ℕ → V) (m : ℕ) : ℕ → V := fun k => π (k + m)

@[simp] theorem shift_zero (π : ℕ → V) (m : ℕ) : shift π m 0 = π m := by
  show π (0 + m) = π m
  rw [Nat.zero_add]

theorem isPath_shift {π : ℕ → V} (h : a.IsPath π) (m : ℕ) : a.IsPath (shift π m) := by
  intro n
  have := h (n + m)
  simpa [shift, Nat.succ_add] using this

theorem pathIn_shift {S : Set V} {π : ℕ → V} (h : a.PathIn S π) (m : ℕ) :
    a.PathIn S (shift π m) :=
  ⟨a.isPath_shift h.1 m, fun _ => h.2 _⟩

theorem consE_shift {f : V → V} {π : ℕ → V} (h : a.ConsE f π) (m : ℕ) :
    a.ConsE f (shift π m) := by
  intro n hn
  have := h (n + m) hn
  simpa [shift, Nat.succ_add] using this

theorem consA_shift {g : V → V} {π : ℕ → V} (h : a.ConsA g π) (m : ℕ) :
    a.ConsA g (shift π m) := by
  intro n hn
  have := h (n + m) hn
  simpa [shift, Nat.succ_add] using this

theorem eveWinsPlay_shift {π : ℕ → V} (m : ℕ) :
    a.EveWinsPlay (shift π m) ↔ a.EveWinsPlay π := by
  have h : a.prioSeq (shift π m) = fun n => a.prioSeq π (n + m) := rfl
  constructor
  · rintro ⟨p, hp, hep⟩
    rw [h] at hp
    exact ⟨p, maxInfOften_shift.1 hp, hep⟩
  · rintro ⟨p, hp, hep⟩
    exact ⟨p, by rw [h]; exact maxInfOften_shift.2 hp, hep⟩

/-- Prefixing a play with one extra vertex. -/
def cons (v : V) (π : ℕ → V) : ℕ → V := fun n => Nat.rec v (fun k _ => π k) n

@[simp] theorem cons_zero (v : V) (π : ℕ → V) : cons v π 0 = v := rfl

@[simp] theorem cons_succ (v : V) (π : ℕ → V) (n : ℕ) : cons v π (n + 1) = π n := rfl

theorem shift_cons_one (v : V) (π : ℕ → V) : shift (cons v π) 1 = π := by
  funext n
  simp [shift]

theorem eveWinsPlay_cons (v : V) (π : ℕ → V) :
    a.EveWinsPlay (cons v π) ↔ a.EveWinsPlay π := by
  have h := a.eveWinsPlay_shift (π := cons v π) 1
  rw [shift_cons_one] at h
  exact h.symm

/-! ### Invariance of winning under a move -/

theorem winsE_step {S : Set V} {f : V → V} {v w : V} (hv : a.WinsE S f v) (hvS : v ∈ S)
    (he : a.E v w) (hf : a.own v → w = f v) : a.WinsE S f w := by
  intro π hπ hπ0 hcons
  have hpath : a.PathIn S (cons v π) := by
    refine ⟨?_, ?_⟩
    · intro n
      cases n with
      | zero => simpa [hπ0] using he
      | succ k => exact hπ.1 k
    · intro n
      cases n with
      | zero => exact hvS
      | succ k => exact hπ.2 k
  have hc : a.ConsE f (cons v π) := by
    intro n hn
    cases n with
    | zero =>
        simp only [cons_zero] at hn ⊢
        simp only [cons_succ]
        rw [hπ0]
        exact hf hn
    | succ k => exact hcons k hn
  have := hv (cons v π) hpath rfl hc
  exact (a.eveWinsPlay_cons v π).1 this

theorem winsA_step {S : Set V} {g : V → V} {v w : V} (hv : a.WinsA S g v) (hvS : v ∈ S)
    (he : a.E v w) (hg : ¬ a.own v → w = g v) : a.WinsA S g w := by
  intro π hπ hπ0 hcons
  have hpath : a.PathIn S (cons v π) := by
    refine ⟨?_, ?_⟩
    · intro n
      cases n with
      | zero => simpa [hπ0] using he
      | succ k => exact hπ.1 k
    · intro n
      cases n with
      | zero => exact hvS
      | succ k => exact hπ.2 k
  have hc : a.ConsA g (cons v π) := by
    intro n hn
    cases n with
    | zero =>
        simp only [cons_zero] at hn ⊢
        simp only [cons_succ]
        rw [hπ0]
        exact hg hn
    | succ k => exact hcons k hn
  intro hwin
  exact hv (cons v π) hpath rfl hc ((a.eveWinsPlay_cons v π).2 hwin)

/-! ### Both players cannot win -/

/-- Both players cannot win from the same vertex. -/
theorem not_winsE_winsA {S : Set V} {f g : V → V} {v : V} (hvS : v ∈ S)
    (hf : a.EveOK S f) (hg : a.AdamOK S g) (hE : a.WinsE S f v) (hA : a.WinsA S g v) :
    False := by
  classical
  -- the play in which both players follow their strategies
  set π : ℕ → V := fun n => Nat.rec v (fun _ w => if a.own w then f w else g w) n with hπdef
  have hstep : ∀ n, π (n + 1) = if a.own (π n) then f (π n) else g (π n) := fun n => rfl
  have hmem : ∀ n, π n ∈ S := by
    intro n
    induction n with
    | zero => exact hvS
    | succ k ih =>
        rw [hstep k]
        by_cases hk : a.own (π k)
        · rw [if_pos hk]; exact (hf _ ih hk).1
        · rw [if_neg hk]; exact (hg _ ih hk).1
  have hpath : a.PathIn S π := by
    refine ⟨fun n => ?_, hmem⟩
    rw [hstep n]
    by_cases hk : a.own (π n)
    · rw [if_pos hk]; exact (hf _ (hmem n) hk).2
    · rw [if_neg hk]; exact (hg _ (hmem n) hk).2
  have hcE : a.ConsE f π := by
    intro n hn
    rw [hstep n, if_pos hn]
  have hcA : a.ConsA g π := by
    intro n hn
    rw [hstep n, if_neg hn]
  exact hA π hpath rfl hcA (hE π hpath rfl hcE)

/-! ### Duality -/

/-- The dual arena: the owners are swapped and the priorities are shifted by one, so that
Adam in `a` is Eve in `a.dual`. -/
def dual : Arena V where
  own := fun v => ¬ a.own v
  E := a.E
  prio := fun v => a.prio v + 1

@[simp] theorem dual_own (v : V) : a.dual.own v ↔ ¬ a.own v := Iff.rfl
@[simp] theorem dual_E (v w : V) : a.dual.E v w ↔ a.E v w := Iff.rfl
@[simp] theorem dual_prio (v : V) : a.dual.prio v = a.prio v + 1 := rfl

@[simp] theorem dual_isPath (π : ℕ → V) : a.dual.IsPath π ↔ a.IsPath π := Iff.rfl
@[simp] theorem dual_pathIn (S : Set V) (π : ℕ → V) : a.dual.PathIn S π ↔ a.PathIn S π :=
  Iff.rfl
@[simp] theorem dual_closed (S : Set V) : a.dual.Closed S ↔ a.Closed S := Iff.rfl

theorem dual_prioSeq (π : ℕ → V) : a.dual.prioSeq π = fun n => a.prioSeq π n + 1 := rfl

theorem dual_consE (f : V → V) (π : ℕ → V) : a.dual.ConsE f π ↔ a.ConsA f π := Iff.rfl

theorem dual_eveOK (S : Set V) (f : V → V) : a.dual.EveOK S f ↔ a.AdamOK S f := Iff.rfl

theorem dual_adamOK (S : Set V) (g : V → V) : a.dual.AdamOK S g ↔ a.EveOK S g := by
  constructor
  · intro h v hv hown
    exact h v hv (by simpa using hown)
  · intro h v hv hown
    exact h v hv (by simpa using hown)

/-! ### Existence of the maximal priority occurring infinitely often -/

section Finite

variable [Fintype V]

theorem exists_maxInfOften_prio (π : ℕ → V) :
    ∃ p, MaxInfOften (a.prioSeq π) p := by
  classical
  obtain ⟨B, hB⟩ : ∃ B, ∀ v : V, a.prio v ≤ B :=
    ⟨(Finset.univ.image a.prio).sup id, fun v =>
      Finset.le_sup (f := id) (Finset.mem_image_of_mem a.prio (Finset.mem_univ v))⟩
  exact exists_maxInfOften (fun n => hB (π n))

theorem not_eveWinsPlay_iff (π : ℕ → V) :
    ¬ a.EveWinsPlay π ↔ ∃ p, MaxInfOften (a.prioSeq π) p ∧ ¬ Even p := by
  obtain ⟨p, hp⟩ := a.exists_maxInfOften_prio π
  constructor
  · intro h
    exact ⟨p, hp, fun hep => h ⟨p, hp, hep⟩⟩
  · rintro ⟨q, hq, hqo⟩ ⟨r, hr, hre⟩
    have : q = r := hq.unique hr
    exact hqo (this ▸ hre)

theorem dual_eveWinsPlay (π : ℕ → V) :
    a.dual.EveWinsPlay π ↔ ¬ a.EveWinsPlay π := by
  classical
  obtain ⟨p, hp⟩ := a.exists_maxInfOften_prio π
  have hdp : MaxInfOften (a.dual.prioSeq π) (p + 1) := by
    rw [dual_prioSeq]
    exact maxInfOften_succ.2 hp
  constructor
  · rintro ⟨q, hq, hqe⟩
    have hq' : q = p + 1 := hq.unique hdp
    subst hq'
    rw [a.not_eveWinsPlay_iff]
    refine ⟨p, hp, ?_⟩
    simpa [Nat.even_add_one] using hqe
  · intro h
    rw [a.not_eveWinsPlay_iff] at h
    obtain ⟨q, hq, hqo⟩ := h
    have : q = p := hq.unique hp
    subst this
    refine ⟨q + 1, hdp, ?_⟩
    simpa [Nat.even_add_one] using hqo

theorem dual_winsE (S : Set V) (f : V → V) (v : V) :
    a.dual.WinsE S f v ↔ a.WinsA S f v := by
  constructor
  · intro h π hπ hπ0 hc
    exact (a.dual_eveWinsPlay π).1 (h π hπ hπ0 hc)
  · intro h π hπ hπ0 hc
    exact (a.dual_eveWinsPlay π).2 (h π hπ hπ0 hc)

theorem dual_winsA (S : Set V) (g : V → V) (v : V) :
    a.dual.WinsA S g v ↔ a.WinsE S g v := by
  constructor
  · intro h π hπ hπ0 hc
    by_contra hcon
    refine h π hπ hπ0 ?_ ((a.dual_eveWinsPlay π).2 hcon)
    intro n hn
    exact hc n (by simpa using hn)
  · intro h π hπ hπ0 hc hwin
    refine (a.dual_eveWinsPlay π).1 hwin ?_
    refine h π hπ hπ0 ?_
    intro n hn
    exact hc n (by simpa using hn)

end Finite

end Arena

end FinGame

end Lax369799Proofs.WordAutomata
