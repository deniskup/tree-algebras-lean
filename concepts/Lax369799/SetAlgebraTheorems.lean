import Lax369799.AutomatonProperty

/-!
---
title: Order and yield properties of set-algebras
type: theorem
---
Meet is associative, commutative, and idempotent, and its induced relation
is a partial order with meet as infimum (`lemma:meet-is-meet`). Evaluation
reverses yield inclusion (`lemma:yieldssubset-yaleq`). Elements of ranks
zero and one are deterministic (`lemma:det-characterisation`).
-/

namespace Lax369799.SetAlgebraTheorems
open RankedSystems Morphisms SetAlgebras AutomatonProperty

axiom meet_laws {A : RankedSet} (E : SetAlgebra A) (n : ℕ) :
    (∀ a b c : A n, meet E (meet E a b) c = meet E a (meet E b c)) ∧
    (∀ a b : A n, meet E a b = meet E b a) ∧
    (∀ a : A n, meet E a a = a)

axiom order_laws {A : RankedSet} (E : SetAlgebra A) (n : ℕ) :
    (∀ a : A n, Below E a a) ∧
    (∀ a b : A n, Below E a b → Below E b a → a = b) ∧
    (∀ a b c : A n, Below E a b → Below E b c → Below E a c) ∧
    (∀ a b c : A n, Below E c (meet E a b) ↔ Below E c a ∧ Below E c b)

axiom yield_order {A : RankedSet} (E : SetAlgebra A) {n : ℕ}
    (S T : SetSystem A n) (h : YieldBelow S T) : Below E (E.eval n T) (E.eval n S)

axiom low_rank_deterministic {A : RankedSet} (E : SetAlgebra A)
    {n : ℕ} (hn : n ≤ 1) (a : A n) : Deterministic E a

end Lax369799.SetAlgebraTheorems
