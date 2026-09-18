import Lax369799.InfiniteRamsey
import Mathlib.Data.Set.Finite.Lattice
import Mathlib.Order.Interval.Finset.Nat

namespace Lax369799Proofs.InfiniteRamsey

theorem infinite_color {C : Type} [Finite C] (s : Set ℕ) (hs : s.Infinite)
    (f : ℕ → C) : ∃ c, {n | n ∈ s ∧ f n = c}.Infinite := by
  classical
  by_contra! h
  apply hs
  exact (Set.finite_iUnion h).subset (fun n hn => Set.mem_iUnion.mpr ⟨f n, hn, rfl⟩)

private structure Row {C : Type} (color : ℕ → ℕ → C) (s : Set ℕ) where
  head : ℕ
  mem : head ∈ s
  shade : C
  tail : Set ℕ
  infinite : tail.Infinite
  subset : tail ⊆ s
  later : ∀ y ∈ tail, head < y
  constant : ∀ y ∈ tail, color head y = shade

private theorem row_exists {C : Type} [Finite C] (color : ℕ → ℕ → C)
    (s : Set ℕ) (hs : s.Infinite) : Nonempty (Row color s) := by
  obtain ⟨x, hx⟩ := hs.nonempty
  have ht : (s \ Set.Iic x).Infinite := hs.sdiff (Set.finite_Iic x)
  obtain ⟨c, hc⟩ := infinite_color _ ht (color x)
  exact ⟨⟨x, hx, c, _, hc, fun _ h => h.1.1,
    fun _ h => Nat.lt_of_not_ge h.1.2, fun _ h => h.2⟩⟩

private noncomputable def row {C : Type} [Finite C] (color : ℕ → ℕ → C)
    (s : {s : Set ℕ // s.Infinite}) : Row color s.val := Classical.choice (row_exists color s.val s.property)

private noncomputable def reservoir {C : Type} [Finite C] (color : ℕ → ℕ → C) :
    ℕ → {s : Set ℕ // s.Infinite}
  | 0 => ⟨Set.univ, Set.infinite_univ⟩
  | n + 1 => ⟨(row color (reservoir color n)).tail, (row color (reservoir color n)).infinite⟩

/--
---
conclusion: Lax369799.InfiniteRamsey.pairs
---
Successively choose a vertex and an infinite tail on which its outgoing
color is constant. Thin the sequence once more to a color occurring
infinitely often. Nested tails give homogeneity of every increasing pair.
-/
theorem pairs {C : Type} [Finite C] (color : ℕ → ℕ → C) :
    ∃ (f : ℕ → ℕ) (c : C), StrictMono f ∧ ∀ i j, i < j → color (f i) (f j) = c := by
  let r := fun n => row color (reservoir color n)
  have nested : Antitone (fun n => (reservoir color n).val) :=
    antitone_nat_of_succ_le (fun n => (r n).subset)
  have hmono : StrictMono (fun n => (r n).head) := by
    apply strictMono_nat_of_lt_succ
    intro n
    exact (r n).later _ (r (n + 1)).mem
  have hrow (i j : ℕ) (hij : i < j) : color (r i).head (r j).head = (r i).shade :=
    (r i).constant _ (nested hij (r j).mem)
  obtain ⟨c, hc⟩ := infinite_color Set.univ Set.infinite_univ (fun n => (r n).shade)
  obtain ⟨g, hg, hgc⟩ := Nat.exists_strictMono_subsequence (fun N => by
    obtain ⟨n, hn, hN⟩ := hc.exists_gt N
    exact ⟨n, hN, hn⟩)
  refine ⟨fun n => (r (g n)).head, c, hmono.comp hg, ?_⟩
  intro i j hij
  exact (hrow (g i) (g j) (hg hij)).trans (hgc i).2

end Lax369799Proofs.InfiniteRamsey
