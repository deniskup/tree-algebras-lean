import Lax369799.SetSystemAlgebras

/-!
---
title: Finite meets in a set-algebra
type: theorem
---
The value of a disjoint family of atomic elements is their meet. This
includes the empty family, whose value is the greatest element. The
universal property follows from the reverse morphism axiom and
monotonicity of evaluation; no continuity axiom is needed.
-/

namespace Lax369799.FiniteAlgebraMeets
open RankedSystems (RankedSet)
open FinitePresentations SetSystemAlgebras

def family {A : RankedSet} {n k : ℕ} (f : Fin k → A n) : FiniteSystem A n where
  size := k
  graph := {
    label := fun i => ⟨n, f i⟩
    initial := Set.univ
    root := ∅
    edge := fun _ d t => ∃ j : Fin n, d = j.val ∧ t = .inr j
    direction_valid := by rintro v d t ⟨j, rfl, _⟩; exact j.isLt }

def value {A : RankedSet} (E : SetAlgebra A) {n k : ℕ} (f : Fin k → A n) : A n :=
  E.eval n (family f)

axiom lower_iff {A : RankedSet} (E : SetAlgebra A) {n k : ℕ}
    (f : Fin k → A n) (x : A n) : Below E x (value E f) ↔ ∀ i, Below E x (f i)

axiom component {A : RankedSet} (E : SetAlgebra A) {n k : ℕ}
    (f : Fin k → A n) (i : Fin k) : Below E (value E f) (f i)

axiom monotone {A : RankedSet} (E : SetAlgebra A) {n k : ℕ}
    (f g : Fin k → A n) (h : ∀ i, Below E (f i) (g i)) : Below E (value E f) (value E g)

end Lax369799.FiniteAlgebraMeets
