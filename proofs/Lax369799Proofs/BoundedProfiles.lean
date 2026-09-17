import Lax369799.FiniteProfiles
import Mathlib.Data.Fintype.Sets
import Mathlib.Data.Finite.Prod
import Mathlib.Data.Finite.Sigma
import Mathlib.Algebra.Order.BigOperators.Group.Finset

namespace Lax369799Proofs.BoundedProfiles
open Lax369799.RankedSystems Lax369799.Morphisms Lax369799.Resolutions
open Lax369799.FiniteProfiles
open Lax369799.FinitePresentations (FiniteSystem)

private theorem small_rank_bound {bound m n : ℕ}
    (σ : Fin m → Fin n) (h : ∀ j, Nat.card {i // σ i = j} ≤ bound) : m ≤ n * bound := by
  classical
  calc
    m = Nat.card (Fin m) := by simp
    _ = Nat.card (Σ j : Fin n, {i // σ i = j}) := (Nat.card_congr (Equiv.sigmaFiberEquiv σ)).symm
    _ = ∑ j : Fin n, Nat.card {i // σ i = j} := Nat.card_sigma
    _ ≤ ∑ _j : Fin n, bound := Finset.sum_le_sum (fun j _ => h j)
    _ = n * bound := by simp

private abbrev BoundedEntry (B : RankedSet) (bound n : ℕ) :=
  {e : ProfileEntry B n // ∀ j, Nat.card {i // e.2.2 i = j} ≤ bound}

private theorem small_entry_finite {B : RankedSet} (hB : RankwiseFinite B) (bound n : ℕ) :
    Finite (BoundedEntry B bound n) := by
  let : ∀ m, Finite (B m) := hB
  let K := n * bound
  let f : BoundedEntry B bound n → (m : Fin (K + 1)) × B m.val × (Fin m.val → Fin n) :=
    fun e => ⟨⟨e.val.1, Nat.lt_succ_of_le (small_rank_bound e.val.2.2 e.property)⟩, e.val.2⟩
  apply Finite.of_injective f
  intro e e' h
  apply Subtype.ext
  have hh := congrArg (fun x : (m : Fin (K + 1)) × B m.val × (Fin m.val → Fin n) =>
    (⟨x.1.val, x.2⟩ : ProfileEntry B n)) h
  exact hh

private def profileCode {A B : RankedSet} (bound : ℕ) (ρ : ∀ n, System A n → B n)
    {n : ℕ} (S : FiniteSystem A n) : Set (BoundedEntry B bound n) × Set (BoundedEntry B bound n) :=
  (fun e => e.val ∈ Profile ρ (trim S.graph),
    fun e => e.val ∈ Profile ρ (uproot (trim S.graph)))

private theorem code_eq_iff {A B : RankedSet} (bound : ℕ) (ρ : ∀ n, System A n → B n)
    {n : ℕ} (S T : FiniteSystem A n) :
    profileCode bound ρ S = profileCode bound ρ T ↔ BoundedProfileEquivalent bound ρ S T := by
  have one (S T : SetSystem A n) :
      (fun e : BoundedEntry B bound n => e.val ∈ Profile ρ S) = (fun e => e.val ∈ Profile ρ T) ↔
        BoundedProfile bound ρ S = BoundedProfile bound ρ T := by
    constructor
    · intro h
      ext e
      change (e ∈ Profile ρ S ∧ (∀ j, Nat.card {i // e.2.2 i = j} ≤ bound)) ↔ (e ∈ Profile ρ T ∧ (∀ j, Nat.card {i // e.2.2 i = j} ≤ bound))
      constructor
      · rintro ⟨he, hs⟩
        exact ⟨(congrFun h ⟨e, hs⟩).mp he, hs⟩
      · rintro ⟨he, hs⟩
        exact ⟨(congrFun h ⟨e, hs⟩).mpr he, hs⟩
    · intro h
      funext e
      apply propext
      have hh := Set.ext_iff.mp h e.val
      change (_ ∧ (∀ j, Nat.card {i // e.val.2.2 i = j} ≤ bound)) ↔ (_ ∧ (∀ j, Nat.card {i // e.val.2.2 i = j} ≤ bound)) at hh
      simpa only [e.property, implies_true, and_true] using hh
  constructor
  · intro h
    exact ⟨(one (trim S.graph) (trim T.graph)).mp (congrArg Prod.fst h),
      (one (uproot (trim S.graph)) (uproot (trim T.graph))).mp (congrArg Prod.snd h)⟩
  · rintro ⟨h, h'⟩
    exact Prod.ext ((one (trim S.graph) (trim T.graph)).mpr h) ((one (uproot (trim S.graph)) (uproot (trim T.graph))).mpr h')

/--
---
conclusion: Lax369799.FiniteProfiles.bounded_profile_finite
---
A variable map with fibres bounded by b has domain size at most n times b.
Thus the possible bounded entries form a finite
set, and initial/root profiles range over two finite powersets.
-/
theorem bounded_profile_finite {A B : RankedSet} (hB : RankwiseFinite B) (bound : ℕ)
    (ρ : ∀ n, System A n → B n) (n : ℕ) :
    Finite (Quot (@BoundedProfileEquivalent A B bound ρ n)) := by
  let : Finite (BoundedEntry B bound n) := small_entry_finite hB bound n
  let f : Quot (@BoundedProfileEquivalent A B bound ρ n) →
      Set (BoundedEntry B bound n) × Set (BoundedEntry B bound n) :=
    Quot.lift (profileCode bound ρ) (fun S T h => (code_eq_iff bound ρ S T).mpr h)
  apply Finite.of_injective f
  intro x y
  induction x using Quot.inductionOn with
  | h S =>
    induction y using Quot.inductionOn with
    | h T =>
      intro h
      exact Quot.sound ((code_eq_iff bound ρ S T).mp h)

end Lax369799Proofs.BoundedProfiles
