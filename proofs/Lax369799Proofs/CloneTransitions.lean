import Lax369799.CloneTransitions
import Lax369799Proofs.FiniteRecurrence
import Lax369799Proofs.FiniteAlgebraMeets

namespace Lax369799Proofs.CloneTransitions
open Lax369799
open RankedSystems (RankedSet)
open SetSystemAlgebras BisimAutomata UnfoldAutomata TransitionEncoding CloneTransitions

private theorem closure_cast {H : Type} (B : ∀ n, Set (Fin n → H)) {p q : ℕ}
    (h : p = q) (b : Fin p → H) (hb : b ∈ Closure B p) :
    (fun i => b (Fin.cast h.symm i)) ∈ Closure B q := by
  cases h
  exact hb

/--
---
conclusion: Lax369799.CloneTransitions.closure_closed
---
Duplicating each component by k and then by m duplicates it by km.
-/
theorem closure_closed {H : Type} (B : ∀ n, Set (Fin n → H)) {n m : ℕ}
    (b : Fin n → H) (hb : b ∈ Closure B n) (hm : 0 < m) : Duplicate b ∈ Closure B (n * m) := by
  obtain ⟨p, k, hp, hk, hpk, c, hc, rfl⟩ := hb
  refine ⟨p, k * m, hp, Nat.mul_pos hk hm,
    (by rw [← Nat.mul_assoc, hpk] : p * (k * m) = n * m), c, hc, ?_⟩
  funext i
  apply congrArg c
  apply Fin.ext
  simp [Duplicate, Fin.divNat, Nat.div_div_eq_div_mul, Nat.mul_comm]

/--
---
conclusion: Lax369799.CloneTransitions.component
---
Each compressed label is the meet of its block of original labels.
-/
theorem component {A : RankedSet} (E : SetAlgebra A) {n k : ℕ}
    (b : Fin (n * k) → A 1) (i : Fin n) (j : Fin k) :
    Below E (compress E b i) (b (finProdFinEquiv (i, j))) :=
  FiniteAlgebraMeets.component E _ j

/--
---
conclusion: Lax369799.CloneTransitions.stabilizes
---
The space of compressed n-tuples is finite. Apply eventual containment
in the recurrent part of the sequence.
-/
theorem stabilizes {A : RankedSet} {V : Type} (E : SetAlgebra A) [Finite (A 1)]
    (T : V → ∀ n, Set (Fin (n + 1) → A 1)) (ν : V) (n : ℕ) :
    ∃ N, ∀ k, N ≤ k → alpha E T ν n k ⊆ beta E T ν n :=
  FiniteRecurrence.eventual_subset _

/--
---
conclusion: Lax369799.CloneTransitions.uniform_stabilization
---
Take the maximum of the thresholds for the finitely many input labels
and arities; the tuple spaces may have different dimensions.
-/
theorem uniform_stabilization {A : RankedSet} {V I : Type} (E : SetAlgebra A)
    [Finite (A 1)] [Finite I] (T : V → ∀ n, Set (Fin (n + 1) → A 1))
    (ν : I → V) (arity : I → ℕ) :
    ∃ N, ∀ i k, N ≤ k → alpha E T (ν i) (arity i) k ⊆ beta E T (ν i) (arity i) := by
  classical
  letI : Fintype I := Fintype.ofFinite I
  choose bound hbound using fun i => stabilizes E T (ν i) (arity i)
  exact ⟨Finset.univ.sup bound, fun i k hk => hbound i k
    ((Finset.le_sup (Finset.mem_univ i)).trans hk)⟩

/--
---
conclusion: Lax369799.CloneTransitions.clone_automaton
---
Decode the unary type codes, apply closure under duplication, and
transport the resulting tuple along the positive target arity.
-/
theorem clone_automaton {P H : Type} [Fintype H] {z : ℕ}
    (B : Set P → ∀ n, Set (Fin n → H)) (leaves : Set P → Set (Fin z))
    (D : WordCondition (Fintype.card H) z) : IsBisimAutomaton (automaton B leaves D) := by
  intro ν n b hb m hm
  have hpos : 0 < (n + 1) * m := Nat.mul_pos (Nat.succ_pos _) hm
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hpos)
  refine ⟨k, hk, ?_⟩
  have hc := closure_closed (B ν) (fun i => (Fintype.equivFin H).symm (b i)) hb hm
  exact closure_cast (B ν) hk _ hc

private def cap {m k : ℕ} (hm : 0 < m) (j : Fin k) : Fin m :=
  ⟨min j.val (m - 1), lt_of_le_of_lt (Nat.min_le_right _ _) (by omega)⟩

private theorem cap_surjective {m k : ℕ} (hm : 0 < m) (hk : m ≤ k) :
    Function.Surjective (cap (k := k) hm) := by
  intro j
  refine ⟨Fin.castLE hk j, ?_⟩
  apply Fin.ext
  dsimp [cap]
  exact Nat.min_eq_left (by have := j.isLt; omega)

/--
---
conclusion: Lax369799.CloneTransitions.refinement
---
Choose a recurrent compression with at least as many copies as the clone.
Cap excess copies at the last old direction. This map is surjective,
and every compressed label lies below its original component.
-/
theorem refinement {A : RankedSet} {V : Type} (E : SetAlgebra A)
    (T : V → ∀ n, Set (Fin (n + 1) → A 1)) (ν : V) {n : ℕ}
    (b : Fin n → A 1) (hb : b ∈ Closure (beta E T ν) n) :
    ∃ (l : ℕ) (c : Fin (l + 1) → A 1), c ∈ T ν l ∧
      ∃ σ : Fin (l + 1) → Fin n, Function.Surjective σ ∧
        ∀ i, Below E (b (σ i)) (c i) := by
  obtain ⟨p, m, hp, hm, hpm, a, ha, rfl⟩ := hb
  obtain ⟨k, hk, l, hpk, c, hc, hcompress⟩ := ha m
  let f : Fin k → Fin m := cap hm
  let σ : Fin (l + 1) → Fin n := fun i => Fin.cast hpm
    (finProdFinEquiv ((Fin.cast hpk.symm i).divNat, f (Fin.cast hpk.symm i).modNat))
  have hf : Function.Surjective f := cap_surjective hm hk
  refine ⟨l, c, hc, σ, ?_, ?_⟩
  · intro i
    let x := Fin.cast hpm.symm i
    obtain ⟨j, hj⟩ := hf x.modNat
    refine ⟨Fin.cast hpk (finProdFinEquiv (x.divNat, j)), ?_⟩
    dsimp only [σ]
    simp only [Fin.cast_cast, Fin.cast_refl, id_eq]
    have hd (x : Fin p) (y : Fin k) : (finProdFinEquiv (x, y)).divNat = x :=
      congrArg Prod.fst (finProdFinEquiv.symm_apply_apply (x, y))
    have hm' (x : Fin p) (y : Fin k) : (finProdFinEquiv (x, y)).modNat = y :=
      congrArg Prod.snd (finProdFinEquiv.symm_apply_apply (x, y))
    rw [hd, hm']
    rw [hj]
    change Fin.cast hpm (finProdFinEquiv (finProdFinEquiv.symm x)) = i
    rw [Equiv.apply_symm_apply]
    exact Fin.ext rfl
  · intro i
    have h := component E (fun j => c (Fin.cast hpk j))
      (Fin.cast hpk.symm i).divNat (Fin.cast hpk.symm i).modNat
    rw [hcompress] at h
    change Below E (a (Fin.cast hpk.symm i).divNat)
      (c (Fin.cast hpk (finProdFinEquiv (finProdFinEquiv.symm (Fin.cast hpk.symm i))))) at h
    simp only [Equiv.apply_symm_apply, Fin.cast_cast, Fin.cast_refl, id_eq] at h
    change Below E (a ((Fin.cast hpm.symm (σ i)).divNat)) (c i)
    dsimp only [σ]
    simp only [Fin.cast_cast, Fin.cast_refl, id_eq]
    have hd (x : Fin p) (y : Fin m) : (finProdFinEquiv (x, y)).divNat = x :=
      congrArg Prod.fst (finProdFinEquiv.symm_apply_apply (x, y))
    rw [hd]
    exact h


end Lax369799Proofs.CloneTransitions
