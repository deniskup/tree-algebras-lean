import Lax369799.DeterministicPieces
import Lax369799Proofs.ContextDecomposition
import Lax369799Proofs.Yields
import Lax369799Proofs.VariableCompression

namespace Lax369799Proofs.DeterministicPieces
open Lax369799.RankedSystems Lax369799.Flattening Lax369799.ContextDecomposition
open Lax369799.AlgebraicDecomposition
open Lax369799.DeterministicPieces (continuation)

private noncomputable def target {A : RankedSet} {k : ℕ} (C : SetContext A k 0) :
    BodyVertex C ⊕ Fin 1 → C.system.Vertex
  | .inl v => v.val
  | .inr _ => holeVertex C

private theorem target_injective {A : RankedSet} {k : ℕ} (C : SetContext A k 0) :
    Function.Injective (target C) := by
  intro s t h
  cases s with
  | inl v =>
    cases t with
    | inl w => exact congrArg Sum.inl (Subtype.ext h)
    | inr j => exact False.elim (v.property h)
  | inr i =>
    cases t with
    | inl w => exact False.elim (w.property h.symm)
    | inr j => exact congrArg Sum.inr (Subsingleton.elim i j)

private theorem piece_total {A : RankedSet} {k : ℕ} (C : SetContext A k 0)
    (hC : C.system.Deterministic) (i : Fin (k + 1)) (v : BodyVertex C)
    (d : ℕ) (hd : d < ((ordinaryPiece C i).label v).1) :
    ∃! t, (ordinaryPiece C i).edge v d t := by
  classical
  have he (t : BodyVertex C ⊕ Fin 1) :
      (ordinaryPiece C i).edge v d t ↔ C.system.graph.edge v.val d (.inl (target C t)) := by
    cases t <;> rfl
  obtain ⟨t, ht, hu⟩ := hC.2.2 v.val d hd
  cases t with
  | inr j => exact Fin.elim0 j
  | inl w =>
    have hs : ∃ s, target C s = w := by
      by_cases h : w = holeVertex C
      · exact ⟨.inr 0, h.symm⟩
      · exact ⟨.inl ⟨w, h⟩, rfl⟩
    obtain ⟨s, hs⟩ := hs
    refine ⟨s, (he s).mpr (by rw [hs]; exact ht), ?_⟩
    intro u hh
    apply target_injective C
    rw [hs]
    exact Sum.inl.inj (hu _ ((he u).mp hh))

private theorem piece_root {A : RankedSet} {k : ℕ} (C : SetContext A k 0)
    (hC : C.system.Deterministic) (i : Fin (k + 1)) : (ordinaryPiece C i).root = ∅ := by
  ext v
  change (v.val ∈ C.system.graph.root) ↔ False
  rw [hC.2.1]
  rfl

private theorem trim_empty {A : RankedSet} {n : ℕ} {V : Type} [Fintype V]
    (G : Presentation A n V) (hi : G.initial = ∅) (hr : G.root = ∅) :
    (trim G).size = 0 := by
  classical
  let : IsEmpty {v // G.Reachable v} := ⟨by
    rintro ⟨v, r, h, _⟩
    rcases h with h | h
    · rw [hi] at h; exact h
    · rw [hr] at h; exact h⟩
  exact Fintype.card_eq_zero

/--
---
conclusion: Lax369799.DeterministicPieces.direction_piece
---
Use the unique successor in the selected hole direction. A self-loop
leaves no initial vertex in the cut piece. Every other successor gives
a unique initial vertex, and cutting edges preserves determinism.
-/
theorem direction_piece {A : RankedSet} {k : ℕ} (C : SetContext A k 0)
    (hC : C.system.Deterministic) (i : Fin k) :
    (i ∈ (boundary C).loops ∧ (trim (ordinaryPiece C i.succ)).size = 0) ∨
    (i ∉ (boundary C).loops ∧ (trim (ordinaryPiece C i.succ)).Deterministic) := by
  classical
  have hd : i.val < (C.system.graph.label (holeVertex C)).1 := by
    rw [ContextDecomposition.hole_label C]; exact i.isLt
  obtain ⟨t, ht, hu⟩ := hC.2.2 (holeVertex C) i.val hd
  cases t with
  | inr j => exact Fin.elim0 j
  | inl w =>
    have hi (v : BodyVertex C) : v ∈ (ordinaryPiece C i.succ).initial ↔ v.val = w := by
      constructor
      · rintro (⟨h, _⟩ | ⟨d, he, hh⟩)
        · exact False.elim (Fin.succ_ne_zero i h)
        · have hd : i = d := Fin.succ_inj.mp he
          subst d
          exact Sum.inl.inj (hu _ hh)
      · intro h
        exact Or.inr ⟨i, rfl, by rw [h]; exact ht⟩
    by_cases hw : w = holeVertex C
    · refine Or.inl ⟨?_, trim_empty _ ?_ (piece_root C hC i.succ)⟩
      · change C.system.graph.edge (holeVertex C) i.val (.inl (holeVertex C))
        rw [hw] at ht; exact ht
      · ext v
        rw [hi v]
        exact ⟨fun h => v.property (h.trans hw), False.elim⟩
    · refine Or.inr ⟨?_, Yields.trim_deterministic _ ⟨w, hw⟩ ?_
        (piece_root C hC i.succ) (piece_total C hC i.succ)⟩
      · intro h
        exact hw (Sum.inl.inj (hu _ h)).symm
      · ext v
        rw [hi v]
        exact ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩

/--
---
conclusion: Lax369799.DeterministicPieces.entry_piece
---
The initial vertex is either the hole, giving the empty entry piece,
or a body vertex, giving its unique initial vertex.
-/
theorem entry_piece {A : RankedSet} {k : ℕ} (C : SetContext A k 0)
    (hC : C.system.Deterministic) :
    ((boundary C).initial ∧ (trim (ordinaryPiece C 0)).size = 0) ∨
    (¬ (boundary C).initial ∧ (trim (ordinaryPiece C 0)).Deterministic) := by
  classical
  obtain ⟨w, hw⟩ := hC.1
  have hi (v : BodyVertex C) : v ∈ (ordinaryPiece C 0).initial ↔ v.val = w := by
    constructor
    · rintro (⟨_, h⟩ | ⟨d, hd, _⟩)
      · simpa only [hw, Set.mem_singleton_iff] using h
      · exact False.elim (Fin.succ_ne_zero d hd.symm)
    · intro h
      exact Or.inl ⟨rfl, by rw [hw]; exact h⟩
  by_cases he : w = holeVertex C
  · refine Or.inl ⟨?_, trim_empty _ ?_ (piece_root C hC 0)⟩
    · change holeVertex C ∈ C.system.graph.initial
      rw [hw, he]; rfl
    · ext v
      rw [hi v]
      exact ⟨fun h => v.property (h.trans he), False.elim⟩
  · refine Or.inr ⟨?_, Yields.trim_deterministic _ ⟨w, he⟩ ?_
      (piece_root C hC 0) (piece_total C hC 0)⟩
    · change holeVertex C ∉ C.system.graph.initial
      rw [hw]
      exact fun h => he h.symm
    · ext v
      rw [hi v]
      exact ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩

private theorem empty_not_deterministic {A : RankedSet} {n : ℕ} (S : SetSystem A n)
    (h : S.size = 0) : ¬ S.Deterministic := by
  rintro ⟨⟨v, _⟩, _⟩
  exact Nat.not_lt_zero _ (lt_of_lt_of_eq v.isLt h)

/--
---
conclusion: Lax369799.DeterministicPieces.continuation_boundary
---
The two alternatives for each piece identify precisely when its optional
system is absent: the missing piece records a direct boundary connection.
-/
theorem continuation_boundary {A : RankedSet} {k : ℕ} (C : SetContext A k 0)
    (hC : C.system.Deterministic) :
    (continuation C 0 = none ↔ (boundary C).initial) ∧
    ∀ i : Fin k, continuation C i.succ = none ↔ i ∈ (boundary C).loops := by
  have aux (i : Fin (k + 1)) (P : Prop)
      (h : (P ∧ (trim (ordinaryPiece C i)).size = 0) ∨
        (¬ P ∧ (trim (ordinaryPiece C i)).Deterministic)) :
      continuation C i = none ↔ P := by
    rcases h with ⟨hp, he⟩ | ⟨hp, hd⟩
    · simp only [continuation, dif_neg (empty_not_deterministic _ he), true_iff]
      exact hp
    · simp only [continuation, dif_pos hd, Option.some_ne_none, false_iff]
      exact hp
  exact ⟨aux 0 _ (entry_piece C hC), fun i => aux i.succ _ (direction_piece C hC i)⟩

/--
---
conclusion: Lax369799.DeterministicPieces.compress_continuations
---
Compress by the target and the optional unary observation. The absent
observation distinguishes direct self-loops, giving the bound |V|+1.
-/
theorem compress_continuations {A : RankedSet} {V : Type} [Finite V] {m n : ℕ}
    (C : SetContext A m 0) (hC : C.system.Deterministic)
    (σ : Fin m → Fin n) (ρ : System A 1 → V) :
    ∃ (m' : ℕ) (τ : Fin m → Fin m') (sectionMap : Fin m' → Fin m),
      (∀ j, τ (sectionMap j) = j) ∧
      (∀ i, σ (sectionMap (τ i)) = σ i) ∧
      (∀ i, (continuation C (sectionMap (τ i)).succ).map ρ =
        (continuation C i.succ).map ρ) ∧
      (∀ i, sectionMap (τ i) ∈ (boundary C).loops ↔ i ∈ (boundary C).loops) ∧
      (∀ j, Nat.card {i // σ (sectionMap i) = j} ≤ Nat.card V + 1) := by
  obtain ⟨m', τ, sectionMap, hs, hσ, ho, hb⟩ :=
    VariableCompression.compress σ (fun i => (continuation C i.succ).map ρ)
  refine ⟨m', τ, sectionMap, hs, hσ, ho, ?_, ?_⟩
  · intro i
    rw [← (continuation_boundary C hC).2, ← (continuation_boundary C hC).2]
    have he := congrArg (fun o : Option V => o = none) (ho i)
    simpa only [Option.map_eq_none_iff] using Iff.of_eq he
  · intro j
    let : Fintype V := Fintype.ofFinite V
    simpa only [Nat.card_eq_fintype_card, Fintype.card_option] using hb j

end Lax369799Proofs.DeterministicPieces
