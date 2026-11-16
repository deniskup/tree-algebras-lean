import Lax369799.Algebras
import Mathlib.Algebra.Ring.Parity

/-!
---
title: Unfold-automata and regular-tree acceptance
type: definition
---
An unfold-automaton has finitely many unary and nullary types. At each
internal vertex it chooses a tuple of unary types, one for each outgoing
direction; at a leaf it chooses a nullary type. Every branch must satisfy
a common regular word condition. Here that condition is represented by a
finite deterministic parity word automaton, with a final-state condition
for finite words. Parity uses the least priority occurring infinitely
often, which must be even.

Acceptance permits a run on any finite system representing the same
regular tree, as in Section 6.3; a run on the input presentation alone is
not required. Both finite branches ending at leaves and infinite branches
are checked.
-/

namespace Lax369799.UnfoldAutomata
open RankedSystems Morphisms Algebras

structure WordCondition (unary nullary : ℕ) where
  states : ℕ
  initial : Fin states
  step : Fin states → (Fin unary ⊕ Fin nullary) → Fin states
  priority : Fin states → ℕ
  final : Set (Fin states)

def WordCondition.run {u z : ℕ} (D : WordCondition u z) (w : ℕ → Fin u) : ℕ → Fin D.states
  | 0 => D.initial
  | n + 1 => D.step (D.run w n) (.inl (w n))

def WordCondition.AcceptsInfinite {u z : ℕ} (D : WordCondition u z)
    (w : ℕ → Fin u) : Prop :=
  ∃ c, Even c ∧ (∀ N, ∃ n, N ≤ n ∧ D.priority (D.run w n) = c) ∧
    ∀ b, b < c → ∃ N, ∀ n, N ≤ n → D.priority (D.run w n) ≠ b

def WordCondition.AcceptsFinite {u z : ℕ} (D : WordCondition u z)
    (w : List (Fin u)) (a : Fin z) : Prop :=
  D.step (w.foldl (fun q b => D.step q (.inl b)) D.initial) (.inr a) ∈ D.final

structure UnfoldAutomaton (A : RankedSet) where
  unary : ℕ
  nullary : ℕ
  transition : ∀ n, A (n + 1) → Set (Fin (n + 1) → Fin unary)
  leafTransition : A 0 → Set (Fin nullary)
  condition : WordCondition unary nullary

abbrev Rank {A : RankedSet} {n : ℕ} (S : System A n) (v : S.val.Vertex) :=
  (S.val.graph.label v).1

/-- An assignment of branch types, before imposing transition constraints. -/
structure Labelling {A : RankedSet} (u z : ℕ) (S : System A 0) where
  edgeType : ∀ v, Fin (Rank S v) → Fin u
  leafType : ∀ v, Rank S v = 0 → Fin z

structure Run {A : RankedSet} (M : UnfoldAutomaton A) (S : System A 0) where
  edgeType : ∀ v, Fin (Rank S v) → Fin M.unary
  leafType : ∀ v, Rank S v = 0 → Fin M.nullary
  transitions : ∀ v k (h : Rank S v = k + 1),
    (fun i => edgeType v (Fin.cast h.symm i)) ∈
      M.transition k (h ▸ (S.val.graph.label v).2)
  leaves : ∀ v (h : Rank S v = 0),
    leafType v h ∈ M.leafTransition (h ▸ (S.val.graph.label v).2)

abbrev Run.toLabelling {A : RankedSet} {M : UnfoldAutomaton A} {S : System A 0}
    (r : Run M S) : Labelling M.unary M.nullary S := ⟨r.edgeType, r.leafType⟩

/-- The automaton imposing only the branch condition. -/
def unrestricted {A : RankedSet} {u z : ℕ} (D : WordCondition u z) : UnfoldAutomaton A :=
  ⟨u, z, fun _ _ => Set.univ, fun _ => Set.univ, D⟩

def Labelling.asRun {A : RankedSet} {u z : ℕ} {S : System A 0}
    (r : Labelling u z S) (D : WordCondition u z) : Run (unrestricted D) S :=
  ⟨r.edgeType, r.leafType, fun _ _ _ => trivial, fun _ _ => trivial⟩

structure FiniteBranch {A : RankedSet} (S : System A 0) (length : ℕ) where
  vertex : Fin (length + 1) → S.val.Vertex
  direction : ∀ i : Fin length, Fin (Rank S (vertex i.castSucc))
  starts : vertex 0 ∈ S.val.graph.initial
  follows : ∀ i, S.val.graph.edge (vertex i.castSucc) (direction i).val (.inl (vertex i.succ))
  ends : Rank S (vertex (Fin.last length)) = 0

structure InfiniteBranch {A : RankedSet} (S : System A 0) where
  vertex : ℕ → S.val.Vertex
  direction : ∀ i, Fin (Rank S (vertex i))
  starts : vertex 0 ∈ S.val.graph.initial
  follows : ∀ i, S.val.graph.edge (vertex i) (direction i).val (.inl (vertex (i + 1)))

def Run.Accepting {A : RankedSet} {M : UnfoldAutomaton A} {S : System A 0}
    (r : Run M S) : Prop :=
  (∀ k (b : FiniteBranch S k), M.condition.AcceptsFinite
    (List.ofFn (fun i => r.edgeType (b.vertex i.castSucc) (b.direction i)))
    (r.leafType (b.vertex (Fin.last k)) b.ends)) ∧
  (∀ b : InfiniteBranch S, M.condition.AcceptsInfinite
    (fun i => r.edgeType (b.vertex i) (b.direction i)))

def Labelling.Accepting {A : RankedSet} {u z : ℕ} {S : System A 0}
    (r : Labelling u z S) (D : WordCondition u z) : Prop := (r.asRun D).Accepting

def Accepts {A : RankedSet} (M : UnfoldAutomaton A) (S : System A 0) : Prop :=
  ∃ T : System A 0, UnfoldEquivalent S.val T.val ∧ ∃ r : Run M T, r.Accepting

def Recognizes {A : RankedSet} (M : UnfoldAutomaton A) (L : Language A) : Prop :=
  ∀ S, S ∈ L ↔ Accepts M S

end Lax369799.UnfoldAutomata
