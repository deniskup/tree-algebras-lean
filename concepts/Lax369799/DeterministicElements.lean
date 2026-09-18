import Lax369799.AutomatonProperty
import Lax369799.UnarySystems

/-!
---
title: Unary normal form of deterministic elements
type: theorem
---
In a set-algebra, every deterministic element of positive rank is a
parallel family of unary values, one at each variable. This is the
characterization in Section 5.1. The set-algebra hypothesis includes
continuity; it is not implicit in an arbitrary substitution algebra.
-/
namespace Lax369799.DeterministicElements
open RankedSystems SetAlgebras AutomatonProperty

/-- Retain a chosen variable and rename it to the sole output variable. -/
def projection {A : RankedSet} {n : ℕ} (S : SetSystem A n) (i : Fin n) : SetSystem A 1 where
  size := S.size
  graph := {
    label := S.graph.label
    initial := S.graph.initial
    root := S.graph.root
    edge := fun v d t => S.graph.edge v d (Sum.map id (fun _ => i) t)
    direction_valid := fun v d _t h => S.graph.direction_valid v d _ h }
  reachable := S.reachable

/-- The disjoint unary letters b_i, with each sole edge going to x_i. -/
def parallel {A : RankedSet} {n : ℕ} (b : Fin n → A 1) : SetSystem A n where
  size := n
  graph := {
    label := fun v => ⟨1, b v⟩
    initial := Set.univ
    root := ∅
    edge := fun v d t => d = 0 ∧ t = .inr v
    direction_valid := by rintro v d t ⟨rfl, _⟩; exact Nat.zero_lt_one }
  reachable := fun v => ⟨v, Or.inl trivial, .refl⟩

axiom unary_normal_form {A : RankedSet} (E : SetAlgebra A) {n : ℕ} (hn : 0 < n)
    (a : A n) : Deterministic E a ↔ ∃ b : Fin n → A 1, E.eval n (parallel b) = a

end Lax369799.DeterministicElements
