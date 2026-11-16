import Lax369799.ExtendedContexts

/-!
---
title: Direction projections of extremal elements
type: theorem
---
In Section 5.3 the ith direction of a rank-k element is evaluated by
retaining only its edge to the ith variable and renaming that variable
to the single output. Extremal elements of positive rank equal the
parallel family of their direction projections (Lemma 92), and each
projection is itself an extremal unary element (Lemma 93).
-/

namespace Lax369799.DirectionProjections
open RankedSystems (RankedSet)
open FinitePresentations FiniteContextualOrder FiniteSyntacticAlgebra FiniteAcceptance
open ExpandedSyntacticAlgebra

def projection {A : RankedSet} {k : ℕ} (a : A k) (i : Fin k) : FiniteSystem A 1 where
  size := 1
  graph := {
    label := fun _ => ⟨k, a⟩
    initial := Set.univ
    root := ∅
    edge := fun _ d t => d = i.val ∧ t = .inr 0
    direction_valid := by rintro _ d t ⟨rfl, _⟩; exact i.isLt }

def direction {A : RankedSet} (E : Algebra A) {k : ℕ} (a : A k) (i : Fin k) : A 1 :=
  E.eval 1 (projection a i)

def parallel {A : RankedSet} {k : ℕ} (b : Fin k → A 1) : FiniteSystem A k :=
  ofSetSystem (DeterministicElements.parallel b)

axiom monotone {A : RankedSet} (L : Algebras.Language A)
    (E : SyntacticAlgebra L) {k : ℕ} (a b : Carrier (Accepting L) k)
    (hab : ClassBelow (Accepting L) a b) (i : Fin k) :
    ClassBelow (Accepting L) (direction E.algebra a i) (direction E.algebra b i)

axiom reconstruction_bound {A : RankedSet} (L : Algebras.Language A)
    (E : SyntacticAlgebra L) {k : ℕ} (a : Carrier (Accepting L) k) :
    ClassBelow (Accepting L) a (E.algebra.eval k (parallel (direction E.algebra a)))

axiom parallel_projection_bound {A : RankedSet} (L : Algebras.Language A)
    (E : SyntacticAlgebra L) {k : ℕ} (b : Fin k → Carrier (Accepting L) 1) (i : Fin k) :
    ClassBelow (Accepting L) (direction E.algebra (E.algebra.eval k (parallel b)) i) (b i)

axiom extremal_decomposition {A : RankedSet} (L : Algebras.Language A)
    (E : SyntacticAlgebra L) {k : ℕ} (hk : 1 ≤ k) (a : Carrier (Accepting L) k)
    (ha : ExtendedContexts.ExtremalElement L E a) :
    E.algebra.eval k (parallel (direction E.algebra a)) = a

axiom extremal_direction {A : RankedSet} (L : Algebras.Language A)
    (hL : Algebras.UnfoldInvariantLanguage L) (hrec : Algebras.Recognizable L)
    (E : SyntacticAlgebra L) {k : ℕ} (a : Carrier (Accepting L) k)
    (ha : ExtendedContexts.ExtremalElement L E a) (i : Fin k) :
    ExtendedContexts.ExtremalElement L E (direction E.algebra a i)

end Lax369799.DirectionProjections
