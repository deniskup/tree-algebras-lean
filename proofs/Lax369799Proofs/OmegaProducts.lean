import Lax369799.OmegaProducts
import Lax369799Proofs.OmegaDeterminization
import Lax369799Proofs.WordFactorization
import Mathlib.Data.Nat.Nth

namespace Lax369799Proofs.OmegaProducts
set_option backward.isDefEq.respectTransparency false
open Lax369799.UnfoldAutomata Lax369799.OmegaDeterminization
open Lax369799.WordFactorization Lax369799.OmegaProducts
open scoped Classical

structure State (M : Type) where
  a : M
  e : M
  inPrefix : Bool
  value : M
  cut : Bool

instance {M : Type} [Finite M] : Finite (State M) :=
  Finite.of_injective (fun s : State M => (s.a, s.e, s.inPrefix, s.value, s.cut)) (by
    intro x y h
    cases x
    cases y
    simp only [Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := h
    rfl)

def Initial {M : Type} [Monoid M] (P : M → M → Prop) (s : State M) : Prop :=
  P s.a s.e ∧ s.e * s.e = s.e ∧ s.a * s.e = s.a ∧
    s.inPrefix = true ∧ s.value = 1 ∧ s.cut = false

def Step {M : Type} [Monoid M] (s : State M) (x : M) (t : State M) : Prop :=
  t.a = s.a ∧ t.e = s.e ∧
    ((t.inPrefix = s.inPrefix ∧ t.value = s.value * x ∧ t.cut = false) ∨
      (s.value * x = (if s.inPrefix then s.a else s.e) ∧
        t.inPrefix = false ∧ t.value = 1 ∧ t.cut = true))

private theorem block_self {M : Type} [Monoid M] (w : ℕ → M) (n : ℕ) : block w n n = 1 := by
  simp [block]

private theorem block_succ {M : Type} [Monoid M] (w : ℕ → M) {i n : ℕ} (h : i ≤ n) :
    block w i (n + 1) = block w i n * w n := by
  rw [WordFactorization.block_append w h (Nat.le_succ n)]
  simp [block]

private theorem fixed_pair {M : Type} [Monoid M] {w : ℕ → M} {r : ℕ → State M}
    (hstep : ∀ n, Step (r n) (w n) (r (n + 1))) (n : ℕ) :
    (r n).a = (r 0).a ∧ (r n).e = (r 0).e := by
  induction n with
  | zero => exact ⟨rfl, rfl⟩
  | succ n ih => exact ⟨(hstep n).1.trans ih.1, (hstep n).2.1.trans ih.2⟩

private theorem cut_fields {M : Type} [Monoid M] {w : ℕ → M} {r : ℕ → State M}
    (hinit : (r 0).cut = false) (hstep : ∀ n, Step (r n) (w n) (r (n + 1)))
    {n : ℕ} (hc : (r n).cut = true) : 0 < n ∧ (r n).inPrefix = false ∧ (r n).value = 1 := by
  cases n with
  | zero => simp [hinit] at hc
  | succ n =>
    rcases (hstep n).2.2 with h | h
    · simp [h.2.2] at hc
    · exact ⟨Nat.succ_pos _, h.2.1, h.2.2.1⟩

private theorem prefix_product {M : Type} [Monoid M] {P : M → M → Prop}
    {w : ℕ → M} {r : ℕ → State M} (hinit : Initial P (r 0))
    (hstep : ∀ n, Step (r n) (w n) (r (n + 1))) (n : ℕ) :
    block w 0 n = if (r n).inPrefix then (r n).value else (r 0).a * (r n).value := by
  induction n with
  | zero => simp [block_self, hinit.2.2.2.1, hinit.2.2.2.2.1]
  | succ n ih =>
    rw [block_succ w (Nat.zero_le _), ih]
    rcases (hstep n).2.2 with h | h
    · rw [h.1, h.2.1]
      cases hp : (r n).inPrefix <;> simp [hp, mul_assoc]
    · rw [h.2.1, h.2.2.1]
      have ha := (fixed_pair hstep n).1
      have he := (fixed_pair hstep n).2
      cases hp : (r n).inPrefix
      · simp only [hp, Bool.false_eq_true, ↓reduceIte] at h ⊢
        rw [mul_assoc, h.1, he, hinit.2.2.1, mul_one]
      · simp only [hp, ↓reduceIte]
        simpa only [hp, Bool.false_eq_true, ↓reduceIte, ha, mul_one] using h.1

private theorem tail_product {M : Type} [Monoid M] {P : M → M → Prop}
    {w : ℕ → M} {r : ℕ → State M} (hinit : Initial P (r 0))
    (hstep : ∀ n, Step (r n) (w n) (r (n + 1))) {i : ℕ}
    (hi : (r i).cut = true) (k : ℕ) :
    (r (i + k)).inPrefix = false ∧
      (block w i (i + k) = (r (i + k)).value ∨
        block w i (i + k) = (r 0).e * (r (i + k)).value) := by
  have hif := cut_fields hinit.2.2.2.2.2 hstep hi
  induction k with
  | zero => simpa only [Nat.add_zero, block_self, hif.2.2] using
      (And.intro hif.2.1 (Or.inl rfl) : (r i).inPrefix = false ∧ ((1 : M) = 1 ∨ 1 = (r 0).e * 1))
  | succ k ih =>
    rw [show i + (k + 1) = i + k + 1 from rfl, block_succ w (by omega)]
    rcases (hstep (i + k)).2.2 with h | h
    · refine ⟨h.1.trans ih.1, ?_⟩
      rw [h.2.1]
      exact ih.2.imp (fun heq => congrArg (· * w (i + k)) heq)
        (fun heq => by rw [heq, mul_assoc])
    · have heq : (r (i + k)).value * w (i + k) = (r 0).e := by
        simpa only [ih.1, Bool.false_eq_true, ↓reduceIte, (fixed_pair hstep (i + k)).2] using h.1
      refine ⟨h.2.1, Or.inr ?_⟩
      rw [h.2.2.1, mul_one]
      rcases ih.2 with hv | hv
      · rw [hv, heq]
      · rw [hv, mul_assoc, heq, hinit.2.1]

private theorem between_cuts {M : Type} [Monoid M] {P : M → M → Prop}
    {w : ℕ → M} {r : ℕ → State M} (hinit : Initial P (r 0))
    (hstep : ∀ n, Step (r n) (w n) (r (n + 1))) {i j : ℕ}
    (hi : (r i).cut = true) (hj : (r j).cut = true) (hij : i < j) :
    block w i j = (r 0).e := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : j ≠ 0)
  have hin : i ≤ n := by omega
  have ht := tail_product hinit hstep hi (n - i)
  rw [Nat.add_sub_of_le hin] at ht
  rcases (hstep n).2.2 with h | h
  · simp [h.2.2] at hj
  · have heq : (r n).value * w n = (r 0).e := by
      simpa only [ht.1, Bool.false_eq_true, ↓reduceIte, (fixed_pair hstep n).2] using h.1
    rw [block_succ w hin]
    rcases ht.2 with hv | hv
    · rw [hv, heq]
    · rw [hv, mul_assoc, heq, hinit.2.1]

theorem sound {M : Type} [Monoid M] {u : ℕ} {f : Fin u → M}
    {P : M → M → Prop} {w : ℕ → Fin u} {r : ℕ → State M}
    (hinit : Initial P (r 0)) (hstep : ∀ n, Step (r n) (f (w n)) (r (n + 1)))
    (hinf : {n | (r n).cut = true}.Infinite) : Accepts f P w := by
  let cut := Nat.nth (fun n => (r n).cut = true)
  have hc (i : ℕ) : (r (cut i)).cut = true := Nat.nth_mem_of_infinite hinf i
  refine ⟨(r 0).a, (r 0).e, cut, hinit.1, hinit.2.1, hinit.2.2.1,
    Nat.nth_strictMono hinf, (cut_fields hinit.2.2.2.2.2 hstep (hc 0)).1, ?_, ?_⟩
  · have hp := prefix_product hinit hstep (cut 0)
    rw [(cut_fields hinit.2.2.2.2.2 hstep (hc 0)).2.1,
      (cut_fields hinit.2.2.2.2.2 hstep (hc 0)).2.2] at hp
    simpa [Function.comp_def] using hp
  · intro i
    exact between_cuts hinit hstep (hc i) (hc (i + 1)) (Nat.nth_strictMono hinf (Nat.lt_succ_self i))

private theorem later (c : ℕ → ℕ) (hc : StrictMono c) (n : ℕ) : ∃ k, n < c k :=
  ⟨n + 1, lt_of_lt_of_le (Nat.lt_succ_self n) (hc.id_le (n + 1))⟩

private noncomputable def upper (c : ℕ → ℕ) (hc : StrictMono c) (n : ℕ) : ℕ :=
  Nat.find (later c hc n)

private theorem upper_spec (c : ℕ → ℕ) (hc : StrictMono c) (n : ℕ) : n < c (upper c hc n) :=
  Nat.find_spec (later c hc n)

private theorem upper_min (c : ℕ → ℕ) (hc : StrictMono c) (n k : ℕ)
    (hk : k < upper c hc n) : c k ≤ n :=
  Nat.le_of_not_gt (Nat.find_min (later c hc n) hk)

private theorem upper_eq_zero (c : ℕ → ℕ) (hc : StrictMono c) {n : ℕ} (hn : n < c 0) :
    upper c hc n = 0 := Nat.eq_zero_of_le_zero (Nat.find_min' _ hn)

private theorem upper_succ (c : ℕ → ℕ) (hc : StrictMono c) (n : ℕ) :
    upper c hc (n + 1) = upper c hc n ∨
      (upper c hc (n + 1) = upper c hc n + 1 ∧ n + 1 = c (upper c hc n)) := by
  have hcur := upper_spec c hc n
  have hnext := upper_spec c hc (n + 1)
  have hle : upper c hc n ≤ upper c hc (n + 1) := by
    by_contra h
    have := upper_min c hc n _ (by omega : upper c hc (n + 1) < upper c hc n)
    omega
  by_cases hn : n + 1 < c (upper c hc n)
  · left
    exact Nat.le_antisymm (Nat.find_min' _ hn) hle
  · have heq : n + 1 = c (upper c hc n) := by omega
    right
    refine ⟨Nat.le_antisymm ?_ ?_, heq⟩
    · apply Nat.find_min'
      rw [heq]
      exact hc (Nat.lt_succ_self _)
    · have hne : upper c hc (n + 1) ≠ upper c hc n := by
        intro h
        rw [h, ← heq] at hnext
        exact (Nat.lt_irrefl _ hnext)
      omega

private def lower (c : ℕ → ℕ) (i : ℕ) : ℕ := if i = 0 then 0 else c (i - 1)

private theorem lower_le (c : ℕ → ℕ) (hc : StrictMono c) (n : ℕ) :
    lower c (upper c hc n) ≤ n := by
  by_cases hi : upper c hc n = 0
  · simp [lower, hi]
  · rw [lower, if_neg hi]
    exact upper_min c hc n (upper c hc n - 1) (by omega)

private noncomputable def witness {M : Type} [Monoid M] (a e : M) (w : ℕ → M)
    (c : ℕ → ℕ) (hc : StrictMono c) (n : ℕ) : State M :=
  ⟨a, e, decide (upper c hc n = 0), block w (lower c (upper c hc n)) n,
    decide (upper c hc n ≠ 0 ∧ n = lower c (upper c hc n))⟩

private theorem witness_initial {M : Type} [Monoid M] {P : M → M → Prop}
    {a e : M} {w : ℕ → M} {c : ℕ → ℕ} (hc : StrictMono c) (hpos : 0 < c 0)
    (hP : P a e) (hee : e * e = e) (hae : a * e = a) :
    Initial P (witness a e w c hc 0) := by
  simp only [Initial, witness, upper_eq_zero c hc hpos, lower, ↓reduceIte,
    block_self, decide_true, ne_eq, not_true_eq_false, false_and, decide_false, and_self, and_true]
  exact ⟨hP, hee, hae⟩

private theorem witness_step {M : Type} [Monoid M] {a e : M} {w : ℕ → M}
    {c : ℕ → ℕ} (hc : StrictMono c) (ha : block w 0 (c 0) = a)
    (he : ∀ i, block w (c i) (c (i + 1)) = e) (n : ℕ) :
    Step (witness a e w c hc n) (w n) (witness a e w c hc (n + 1)) := by
  refine ⟨rfl, rfl, ?_⟩
  rcases upper_succ c hc n with hsame | ⟨hnext, hboundary⟩
  · left
    have hlo := lower_le c hc n
    change decide (upper c hc (n + 1) = 0) = decide (upper c hc n = 0) ∧
      block w (lower c (upper c hc (n + 1))) (n + 1) =
        block w (lower c (upper c hc n)) n * w n ∧
      decide (upper c hc (n + 1) ≠ 0 ∧ n + 1 = lower c (upper c hc (n + 1))) = false
    rw [hsame, block_succ w hlo]
    simp only [decide_eq_false_iff_not, not_and]
    exact ⟨True.intro, True.intro, fun _ h => by omega⟩
  · right
    have hacc : block w (lower c (upper c hc n)) n * w n =
        if decide (upper c hc n = 0) then a else e := by
      rw [← block_succ w (lower_le c hc n), hboundary]
      by_cases hi : upper c hc n = 0
      · simpa [hi, lower] using ha
      · have hi' : upper c hc n - 1 + 1 = upper c hc n := by omega
        simpa only [lower, if_neg hi, decide_eq_false hi, Bool.false_eq_true, ↓reduceIte, hi']
          using he (upper c hc n - 1)
    have hlo : lower c (upper c hc n + 1) = c (upper c hc n) := by simp [lower]
    change block w (lower c (upper c hc n)) n * w n =
        (if decide (upper c hc n = 0) then a else e) ∧
      decide (upper c hc (n + 1) = 0) = false ∧
      block w (lower c (upper c hc (n + 1))) (n + 1) = 1 ∧
      decide (upper c hc (n + 1) ≠ 0 ∧ n + 1 = lower c (upper c hc (n + 1))) = true
    rw [hnext, hlo, ← hboundary, block_self]
    simpa using hacc

private theorem witness_cut {M : Type} [Monoid M] {a e : M} {w : ℕ → M}
    {c : ℕ → ℕ} (hc : StrictMono c) (i : ℕ) :
    (witness a e w c hc (c i)).cut = true := by
  have hu : upper c hc (c i) = i + 1 := by
    apply Nat.le_antisymm
    · exact Nat.find_min' _ (hc (Nat.lt_succ_self _))
    · have h := upper_spec c hc (c i)
      by_contra hn
      have := hc.monotone (show upper c hc (c i) ≤ i by omega)
      omega
  simp [witness, hu, lower]

theorem complete {M : Type} [Monoid M] {u : ℕ} {f : Fin u → M}
    {P : M → M → Prop} {w : ℕ → Fin u} (h : Accepts f P w) :
    ∃ r : ℕ → State M, Initial P (r 0) ∧
      (∀ n, Step (r n) (f (w n)) (r (n + 1))) ∧ {n | (r n).cut = true}.Infinite := by
  obtain ⟨a, e, c, hP, hee, hae, hc, hpos, ha, he⟩ := h
  refine ⟨witness a e (f ∘ w) c hc, witness_initial hc hpos hP hee hae,
    witness_step hc ha he, ?_⟩
  apply Set.Infinite.mono (s := Set.range c)
  · rintro n ⟨i, rfl⟩
    exact witness_cut hc i
  · exact Set.infinite_range_of_injective hc.injective

/--
---
conclusion: Lax369799.OmegaProducts.regular
---
A Büchi automaton guesses a linked pair, accumulates the prefix and
successive block products, and marks every reset. Infinitely many resets
give a factorization; a factorization supplies an accepting run. Safra
determinization and appearance records then give a parity condition.
-/
theorem regular {M : Type} [Monoid M] [Finite M] {u z : ℕ}
    (f : Fin u → M) (P : M → M → Prop) :
    ∃ D : WordCondition u z, ∀ w, D.AcceptsInfinite w ↔ Accepts f P w := by
  classical
  letI : Fintype (State M) := Fintype.ofFinite (State M)
  let e := Fintype.equivFin (State M)
  let B : Buchi u := {
    states := Fintype.card (State M)
    initial := {q | Initial P (e.symm q)}
    transition := fun q b t => Step (e.symm q) (f b) (e.symm t)
    accepting := {q | (e.symm q).cut = true} }
  obtain ⟨D, hD⟩ := OmegaDeterminization.determinization (z := z) B
  refine ⟨D, fun w => (hD w).trans ?_⟩
  constructor
  · rintro ⟨r, hi, hs, hinf⟩
    exact sound (r := fun n => e.symm (r n)) hi hs hinf
  · intro h
    obtain ⟨r, hi, hs, hinf⟩ := complete h
    refine ⟨fun n => e (r n), ?_, ?_, ?_⟩
    · simpa only [B, Set.mem_setOf_eq, e.symm_apply_apply] using hi
    · simpa only [B, e.symm_apply_apply] using hs
    · simpa only [B, Set.mem_setOf_eq, e.symm_apply_apply] using hinf

end Lax369799Proofs.OmegaProducts
