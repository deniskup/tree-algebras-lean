import Lax369799.AutomatonProperty

/-!
---
title: Planted normal contexts and deterministic witnesses
type: definition
---
A planted normal context records the hole's root mark and self-loop
directions, together with its unary pieces. Planting merges the original
initial and root marks. The unary components of the witness construction
retain these loops; its outer presentation retains the root mark. This
extends the construction of Section 5 to ordinary holes with arbitrary
boundary data. The extremal choice and comparison inequalities require
separate proofs.
-/

namespace Lax369799.ExtremalContexts
open RankedSystems Flattening SetAlgebras AutomatonProperty

structure Boundary (k : ℕ) where
  root : Prop
  loops : Set (Fin k)

/-- The root piece has index zero; direction i uses piece i+1. -/
def normalPresentation {A : RankedSet} {k : ℕ} (B : Boundary k)
    (m : Fin (k + 1) → A 1) : Presentation (WithHole A k) 0 (Fin (k + 2)) where
  label := Fin.cases ⟨k, Sum.inr ⟨rfl⟩⟩ (fun i => ⟨1, Sum.inl (m i)⟩)
  initial := ∅
  root := fun v => v = (0 : Fin (k + 1)).succ ∨ (v = 0 ∧ B.root)
  edge := fun v d t => Fin.cases
    ((∃ i : Fin k, d = i.val ∧ t = .inl i.succ.succ) ∨
      (∃ i : Fin k, i ∈ B.loops ∧ d = i.val ∧ t = .inl 0))
    (fun _ => d = 0 ∧ t = .inl 0) v
  direction_valid := by
    intro v d t
    refine Fin.cases ?_ (fun i => ?_) v
    · rintro (⟨i, rfl, _⟩ | ⟨i, _, rfl, _⟩) <;> exact i.isLt
    · rintro ⟨rfl, _⟩; exact Nat.zero_lt_one

def normalSystem {A : RankedSet} {k : ℕ} (B : Boundary k)
    (m : Fin (k + 1) → A 1) : SetSystem (WithHole A k) 0 where
  size := k + 2
  graph := normalPresentation B m
  reachable := by
    let G := normalPresentation B m
    have h1 : G.Reachable (0 : Fin (k + 1)).succ :=
      ⟨_, Or.inr (Or.inl rfl), .refl⟩
    have h0 : G.Reachable 0 := by
      obtain ⟨r, hr, hp⟩ := h1
      exact ⟨r, hr, hp.tail ⟨0, rfl, rfl⟩⟩
    intro v
    refine Fin.cases h0 (fun i => ?_) v
    refine Fin.cases h1 (fun j => ?_) i
    obtain ⟨r, hr, hp⟩ := h0
    exact ⟨r, hr, hp.tail ⟨j.val, Or.inl ⟨j, rfl, rfl⟩⟩⟩

def normalContext {A : RankedSet} {k : ℕ} (B : Boundary k)
    (m : Fin (k + 1) → A 1) : SetContext A k 0 where
  system := normalSystem B m
  one_hole := by
    change ∃! v : Fin (k + 2), IsHole ((normalPresentation B m).label v)
    refine ⟨0, ⟨⟨rfl⟩, rfl⟩, ?_⟩
    intro v
    refine Fin.cases (fun _ => rfl) (fun i h => ?_) v
    obtain ⟨h, he⟩ := h
    cases he

/-- Unary component U_i, with the retained loop directions at its a-vertex. -/
def component {A : RankedSet} {k : ℕ} (B : Boundary k)
    (m : Fin (k + 1) → A 1) (a : A k) (i : Fin k) : SetSystem A 1 where
  size := k + 1
  graph := {
    label := Fin.cases ⟨k, a⟩ (fun j => ⟨1, m j.succ⟩)
    initial := {0}
    root := ∅
    edge := fun v d t => Fin.cases
      ((∃ j : Fin k, d = j.val ∧ t = .inl j.succ) ∨
        (∃ j : Fin k, j ∈ B.loops ∧ d = j.val ∧ t = .inl 0) ∨
        (d = i.val ∧ t = .inr 0))
      (fun _ => d = 0 ∧ t = .inl 0) v
    direction_valid := by
      intro v d t
      refine Fin.cases ?_ (fun j => ?_) v
      · rintro (⟨j, rfl, _⟩ | ⟨j, _, rfl, _⟩ | ⟨rfl, _⟩)
        · exact j.isLt
        · exact j.isLt
        · exact i.isLt
      · rintro ⟨rfl, _⟩; exact Nat.zero_lt_one }
  reachable := by
    intro v
    refine ⟨0, Or.inl rfl, ?_⟩
    refine Fin.cases Relation.ReflTransGen.refl (fun j => ?_) v
    exact Relation.ReflTransGen.refl.tail ⟨j.val, Or.inl ⟨j, rfl, rfl⟩⟩

/-- The outer presentation uses only unary labels. -/
def deltaPattern {A : RankedSet} {k : ℕ} (B : Boundary k)
    (m : Fin (k + 1) → A 1) (a : A k) : SetSystem (SetSystem A) k where
  size := k + 1
  graph := {
    label := Fin.cases ⟨1, atomic (m 0)⟩ (fun i => ⟨1, component B m a i⟩)
    initial := fun v => v ≠ 0
    root := fun v => v = 0 ∨ B.root
    edge := fun v d t => d = 0 ∧ Fin.cases
      (∃ i : Fin k, t = .inl i.succ)
      (fun i => t = .inr i) v
    direction_valid := by
      rintro v d t ⟨rfl, _⟩
      refine Fin.cases Nat.zero_lt_one (fun _ => Nat.zero_lt_one) v }
  reachable := by
    intro v
    refine ⟨v, ?_, .refl⟩
    refine Fin.cases (Or.inr (Or.inl rfl)) (fun i => Or.inl (Fin.succ_ne_zero i)) v

noncomputable def delta {A : RankedSet} {k : ℕ} (B : Boundary k)
    (m : Fin (k + 1) → A 1) (a : A k) : SetSystem A k :=
  flatten (deltaPattern B m a)

axiom delta_deterministic {A : RankedSet} (E : SetAlgebra A) {k : ℕ}
    (B : Boundary k) (m : Fin (k + 1) → A 1) (a : A k) :
    Deterministic E (E.eval k (delta B m a))

abbrev Data (A : RankedSet) (k : ℕ) := Boundary k × (Fin (k + 1) → A 1)

/-- Smaller data have more boundary marks and smaller unary values. -/
def DataBelow {A : RankedSet} (E : SetAlgebra A) {k : ℕ} (x y : Data A k) : Prop :=
  (y.1.root → x.1.root) ∧ y.1.loops ⊆ x.1.loops ∧ ∀ i, Below E (x.2 i) (y.2 i)

def Accepts {A : RankedSet} (E : SetAlgebra A) (f : A 0) {k : ℕ}
    (a : A k) (x : Data A k) : Prop :=
  Below E f (E.eval 0 (plug (normalContext x.1 x.2) (atomic a)))

/-- Finite minimization over boundary data as well as the unary pieces. -/
axiom extremal_choice {A : RankedSet} (E : SetAlgebra A) (hA : RankwiseFinite A)
    (f : A 0) {k : ℕ} (a : A k) (x : Data A k) (hx : Accepts E f a x) :
    ∃ y : Data A k, DataBelow E y x ∧ Accepts E f a y ∧
      ∀ z : Data A k, DataBelow E z y → Accepts E f a z → DataBelow E y z

end Lax369799.ExtremalContexts
