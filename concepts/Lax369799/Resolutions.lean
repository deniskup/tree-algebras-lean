import Lax369799.Algebras
import Mathlib.SetTheory.Cardinal.Finite

/-!
---
title: Resolutions and bounded profiles
type: definition
---
A resolution consists of a system and a map from its variables to those of
the target set-system, such that the renamed system maps into the target.
A flatten-resolution resolves both the outer pattern and its labels,
keeping track of a separate variable map at each vertex (Section 2.9).

For a recognising evaluation, a profile records the values and variable
maps of resolutions. A map is small when each fibre has at most as many
elements as the unary sort of the algebra. Small profiles and small root
profiles are the finite summaries used in Section 4.3.
-/

namespace Lax369799.Resolutions
open RankedSystems Morphisms Flattening Algebras

def rename {A : RankedSet} {m n : ℕ} (σ : Fin m → Fin n)
    (S : SetSystem A m) : SetSystem A n where
  size := S.size
  graph := {
    label := S.graph.label
    initial := S.graph.initial
    root := S.graph.root
    edge := fun v d t => ∃ s, S.graph.edge v d s ∧ t = Sum.map id σ s
    direction_valid := by
      rintro v d t ⟨s, hs, _⟩
      exact S.graph.direction_valid v d s hs }
  reachable := by
    intro v
    obtain ⟨r, hr, hp⟩ := S.reachable v
    refine ⟨r, hr, Relation.ReflTransGen.mono ?_ r v hp⟩
    rintro a b ⟨d, hd⟩
    exact ⟨d, .inl b, hd, rfl⟩

def IsResolution {A : RankedSet} {m n : ℕ} (S : SetSystem A n)
    (T : System A m) (σ : Fin m → Fin n) : Prop :=
  Nonempty (Morphism (rename σ T.val) S)

structure FlattenResolution {A : RankedSet} {n : ℕ}
    (S : SetSystem (SetSystem A) n) (T : System (System A) n) where
  vertex : T.val.Vertex → S.Vertex
  variableMap : ∀ v, Fin (T.val.graph.label v).1 → Fin (S.graph.label (vertex v)).1
  initial : ∀ v, v ∈ T.val.graph.initial → vertex v ∈ S.graph.initial
  resolves : ∀ v, IsResolution (Inner S (vertex v)) (T.val.graph.label v).2 (variableMap v)
  transition : ∀ v (i : Fin (T.val.graph.label v).1) w,
    T.val.graph.edge v i.val (.inl w) → S.graph.edge (vertex v) (variableMap v i).val (.inl (vertex w))
  exit : ∀ v (i : Fin (T.val.graph.label v).1) j,
    T.val.graph.edge v i.val (.inr j) → S.graph.edge (vertex v) (variableMap v i).val (.inr j)

abbrev ProfileEntry (B : RankedSet) (n : ℕ) := (m : ℕ) × B m × (Fin m → Fin n)

def SmallMap (B : RankedSet) {m n : ℕ} (σ : Fin m → Fin n) : Prop :=
  ∀ j, Nat.card {i // σ i = j} ≤ Nat.card (B 1)

def Profile {A B : RankedSet} (ρ : ∀ n, System A n → B n) {n : ℕ}
    (S : SetSystem A n) : Set (ProfileEntry B n) :=
  {e | ∃ T : System A e.1, IsResolution S T e.2.2 ∧ ρ e.1 T = e.2.1}

def SmallProfile {A B : RankedSet} (ρ : ∀ n, System A n → B n) {n : ℕ}
    (S : SetSystem A n) : Set (ProfileEntry B n) :=
  {e | e ∈ Profile ρ S ∧ SmallMap B e.2.2}

def ProfileEquivalent {A B : RankedSet} (ρ : ∀ n, System A n → B n) {n : ℕ}
    (S T : SetSystem A n) : Prop :=
  Profile ρ S = Profile ρ T ∧ Profile ρ (uproot S) = Profile ρ (uproot T)

def SmallProfileEquivalent {A B : RankedSet} (ρ : ∀ n, System A n → B n) {n : ℕ}
    (S T : SetSystem A n) : Prop :=
  SmallProfile ρ S = SmallProfile ρ T ∧ SmallProfile ρ (uproot S) = SmallProfile ρ (uproot T)

end Lax369799.Resolutions
