import Lax369799.SyntacticAlgebraTheorems
import Mathlib.Data.Fintype.Sets
import Mathlib.Data.Finite.Prod
import Mathlib.Data.Finite.Sigma
import Mathlib.Algebra.Order.BigOperators.Group.Finset

namespace Lax369799Proofs.Profiles
open Lax369799.RankedSystems Lax369799.Morphisms Lax369799.Resolutions

private theorem small_rank_bound {B : RankedSet} {m n : ℕ}
    (σ : Fin m → Fin n) (h : SmallMap B σ) : m ≤ n * Nat.card (B 1) := by
  classical
  calc
    m = Nat.card (Fin m) := by simp
    _ = Nat.card (Σ j : Fin n, {i // σ i = j}) := (Nat.card_congr (Equiv.sigmaFiberEquiv σ)).symm
    _ = ∑ j : Fin n, Nat.card {i // σ i = j} := Nat.card_sigma
    _ ≤ ∑ _j : Fin n, Nat.card (B 1) := Finset.sum_le_sum (fun j _ => h j)
    _ = n * Nat.card (B 1) := by simp

private abbrev SmallEntry (B : RankedSet) (n : ℕ) :=
  {e : ProfileEntry B n // SmallMap B e.2.2}

private theorem small_entry_finite {B : RankedSet} (hB : RankwiseFinite B) (n : ℕ) :
    Finite (SmallEntry B n) := by
  let : ∀ m, Finite (B m) := hB
  let K := n * Nat.card (B 1)
  let f : SmallEntry B n → (m : Fin (K + 1)) × B m.val × (Fin m.val → Fin n) :=
    fun e => ⟨⟨e.val.1, Nat.lt_succ_of_le (small_rank_bound e.val.2.2 e.property)⟩, e.val.2⟩
  apply Finite.of_injective f
  intro e e' h
  apply Subtype.ext
  have hh := congrArg (fun x : (m : Fin (K + 1)) × B m.val × (Fin m.val → Fin n) =>
    (⟨x.1.val, x.2⟩ : ProfileEntry B n)) h
  exact hh

private def profileCode {A B : RankedSet} (ρ : ∀ n, System A n → B n)
    {n : ℕ} (S : SetSystem A n) : Set (SmallEntry B n) × Set (SmallEntry B n) :=
  (fun e => e.val ∈ Profile ρ S, fun e => e.val ∈ Profile ρ (uproot S))

private theorem code_eq_iff {A B : RankedSet} (ρ : ∀ n, System A n → B n)
    {n : ℕ} (S T : SetSystem A n) :
    profileCode ρ S = profileCode ρ T ↔ SmallProfileEquivalent ρ S T := by
  have one (S T : SetSystem A n) :
      (fun e : SmallEntry B n => e.val ∈ Profile ρ S) = (fun e => e.val ∈ Profile ρ T) ↔
        SmallProfile ρ S = SmallProfile ρ T := by
    constructor
    · intro h
      ext e
      change (e ∈ Profile ρ S ∧ SmallMap B e.2.2) ↔ (e ∈ Profile ρ T ∧ SmallMap B e.2.2)
      constructor
      · rintro ⟨he, hs⟩
        exact ⟨(congrFun h ⟨e, hs⟩).mp he, hs⟩
      · rintro ⟨he, hs⟩
        exact ⟨(congrFun h ⟨e, hs⟩).mpr he, hs⟩
    · intro h
      funext e
      apply propext
      have hh := Set.ext_iff.mp h e.val
      change (_ ∧ SmallMap B e.val.2.2) ↔ (_ ∧ SmallMap B e.val.2.2) at hh
      simpa only [e.property, and_true] using hh
  constructor
  · intro h
    exact ⟨(one S T).mp (congrArg Prod.fst h),
      (one (uproot S) (uproot T)).mp (congrArg Prod.snd h)⟩
  · rintro ⟨h, h'⟩
    exact Prod.ext ((one S T).mpr h) ((one (uproot S) (uproot T)).mpr h')

/--
---
conclusion: Lax369799.SyntacticAlgebraTheorems.small_profile_finite
---
A small variable map into n variables has domain size at most n times
the size of the unary sort. Thus the possible small entries form a finite
set, and initial/root profiles range over two finite powersets.
-/
theorem small_profile_finite {A B : RankedSet} (hB : RankwiseFinite B)
    (ρ : ∀ n, System A n → B n) (n : ℕ) :
    Finite (Quot (@SmallProfileEquivalent A B ρ n)) := by
  let : Finite (SmallEntry B n) := small_entry_finite hB n
  let f : Quot (@SmallProfileEquivalent A B ρ n) →
      Set (SmallEntry B n) × Set (SmallEntry B n) :=
    Quot.lift (profileCode ρ) (fun S T h => (code_eq_iff ρ S T).mpr h)
  apply Finite.of_injective f
  intro x y
  induction x using Quot.inductionOn with
  | h S =>
    induction y using Quot.inductionOn with
    | h T =>
      intro h
      exact Quot.sound ((code_eq_iff ρ S T).mp h)

end Lax369799Proofs.Profiles
