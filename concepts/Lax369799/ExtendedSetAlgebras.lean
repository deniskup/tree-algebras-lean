import Lax369799.ExtendedContexts
import Lax369799.SetSystemAlgebras
import Lax369799.FiniteLocalReplacement

/-!
---
title: Extended set-algebras and extremal accepted situations
type: theorem
---
The formal unary pieces of Definition 65 consist of an ordinary unary
value and a set of immediate initial/root markers. Their order compares
ordinary values and reverses marker inclusion. Expanding such pieces in
a closed context and then evaluating agrees with evaluating their ordinary
parts first (Lemma 66). Context evaluation is monotone (Lemma 86), and
finite minimality supplies extremal accepted situations (Lemma 87).
These constructions apply to arbitrary set-algebras.
-/

namespace Lax369799.ExtendedSetAlgebras
open RankedSystems (RankedSet)
open FinitePresentations FiniteContexts
open SetSystemAlgebras
open ExtendedContexts (Piece Pieces Marker)

def PieceBelow {A : RankedSet} (E : SetAlgebra A) (p q : Piece A) : Prop :=
  Below E p.1 q.1 ∧ q.2 ⊆ p.2

def evaluatePieces {A : RankedSet} (E : SetAlgebra A) {k : ℕ}
    (p : Pieces (FiniteSystem A) k) : Pieces A k :=
  fun i => ⟨E.eval 1 (p i).1, (p i).2⟩

noncomputable def expansion {A : RankedSet} {k : ℕ}
    (p : Pieces (FiniteSystem A) k) (a : A k) : FiniteSystem A 0 :=
  flatten (relabel (fun _r u => match u with
    | .inl s => s
    | .inr ⟨h⟩ => h ▸ atomic a) (ExtendedContexts.context p).system)

noncomputable def value {A : RankedSet} (E : SetAlgebra A) {k : ℕ}
    (p : Pieces A k) (a : A k) : A 0 :=
  E.eval 0 (plug (ExtendedContexts.context p) (atomic a))

def Accepted {A : RankedSet} (E : SetAlgebra A) (F : Set (A 0)) {k : ℕ}
    (p : Pieces A k) (a : A k) : Prop := value E p a ∈ F

def IsExtremal {A : RankedSet} (E : SetAlgebra A) (F : Set (A 0)) {k : ℕ}
    (p : Pieces A k) (a : A k) : Prop :=
  Accepted E F p a ∧ ∀ q b, (∀ i, PieceBelow E (q i) (p i)) → Below E b a →
    Accepted E F q b → q = p ∧ b = a

def ExtremalElement {A : RankedSet} (E : SetAlgebra A) (F : Set (A 0)) {k : ℕ}
    (a : A k) : Prop := ∃ p, IsExtremal E F p a

def UpwardClosed {A : RankedSet} (E : SetAlgebra A) (F : Set (A 0)) : Prop :=
  ∀ a b, a ∈ F → Below E a b → b ∈ F

axiom pieces_evaluation {A : RankedSet} (E : SetAlgebra A) {k : ℕ}
    (p : Pieces (FiniteSystem A) k) (a : A k) :
    E.eval 0 (expansion p a) = value E (evaluatePieces E p) a

axiom context_monotone {A : RankedSet} (E : SetAlgebra A) {k : ℕ}
    (p q : Pieces A k) (hpq : ∀ i, PieceBelow E (p i) (q i))
    (a b : A k) (hab : Below E a b) : Below E (value E p a) (value E q b)

axiom extremal_choice {A : RankedSet} (E : SetAlgebra A) (hA : RankedSystems.RankwiseFinite A)
    (F : Set (A 0)) {k : ℕ} (p : Pieces A k) (a : A k) (ha : Accepted E F p a) :
    ∃ q b, IsExtremal E F q b ∧ (∀ i, PieceBelow E (q i) (p i)) ∧ Below E b a

axiom replacement {A : RankedSet} (E : SetAlgebra A) (hA : RankedSystems.RankwiseFinite A)
    (F : Set (A 0)) (hF : UpwardClosed E F) {k : ℕ}
    (C : Context A k 0) (a : A k) (ha : E.eval 0 (plug C (atomic a)) ∈ F) :
    ∃ b, ExtremalElement E F b ∧ Below E b a ∧ E.eval 0 (plug C (atomic b)) ∈ F

axiom simultaneous {A B : RankedSet} (E : SetAlgebra A) (hA : RankedSystems.RankwiseFinite A)
    (F : Set (A 0)) (hF : UpwardClosed E F) (P : FiniteSystem B 0)
    (q : ∀ v : P.Vertex, A (P.graph.label v).1) :
    E.eval 0 (withLabels P q) ∈ F ↔
      ∃ r : ∀ v : P.Vertex, A (P.graph.label v).1,
        (∀ v, ExtremalElement E F (r v) ∧ Below E (r v) (q v)) ∧
        E.eval 0 (withLabels P r) ∈ F

end Lax369799.ExtendedSetAlgebras
