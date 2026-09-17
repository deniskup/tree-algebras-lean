import Lax369799.Algebras

/-!
---
title: Set-algebras
type: definition
---
A set-algebra evaluates set-systems and satisfies the unit, flattening,
unfold-invariance, morphism, and continuity axioms of Definition 4.1.
The disjoint union of atomic systems defines meet; the induced order has
`a ≤ b` exactly when `a ∧ b = a`. Morphisms reverse this order, while
continuity says that a common lower bound for all yields is a lower bound
for the original set-system. Both initial and root yields occur here.
-/

namespace Lax369799.SetAlgebras
open RankedSystems Morphisms Flattening

noncomputable def meetOf {A : RankedSet} (eval : ∀ n, SetSystem A n → A n)
    {n : ℕ} (a b : A n) : A n := eval n (sum (atomic a) (atomic b))

def BelowOf {A : RankedSet} (eval : ∀ n, SetSystem A n → A n)
    {n : ℕ} (a b : A n) : Prop := meetOf eval a b = a

structure SetAlgebra (A : RankedSet) where
  eval : ∀ n, SetSystem A n → A n
  unit : ∀ n (a : A n), eval n (atomic a) = a
  associative : ∀ n (S : SetSystem (SetSystem A) n),
    eval n (relabel eval S) = eval n (flatten S)
  unfold_invariant : ∀ n (S T : SetSystem A n),
    UnfoldEquivalent S T → eval n S = eval n T
  morphism : ∀ n (S T : SetSystem A n), Nonempty (Morphism S T) →
    BelowOf eval (eval n T) (eval n S)
  continuity : ∀ n (S : SetSystem A n) (a : A n),
    (∀ T, Yield S T → BelowOf eval a (eval n T)) → BelowOf eval a (eval n S)

noncomputable def meet {A : RankedSet} (E : SetAlgebra A) {n : ℕ} (a b : A n) : A n :=
  meetOf E.eval a b

def Below {A : RankedSet} (E : SetAlgebra A) {n : ℕ} (a b : A n) : Prop :=
  BelowOf E.eval a b

structure SetAlgebraMorphism {A B : RankedSet} (E : SetAlgebra A) (F : SetAlgebra B) where
  map : RankedMap A B
  commutes : ∀ n (S : SetSystem A n), F.eval n (relabel map S) = map n (E.eval n S)

end Lax369799.SetAlgebras
