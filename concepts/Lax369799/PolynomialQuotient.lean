import Lax369799.PolynomialContexts

/-!
---
title: Quotients by polynomial acceptance tests
type: theorem
---
Testing all closed polynomial contexts against an accepting set defines
an algebra congruence. Evaluation descends to the quotient, the quotient
preserves recognition, and finite sorts remain finite.
-/
namespace Lax369799.PolynomialQuotient
open RankedSystems Algebras PolynomialContexts

abbrev Carrier {B : RankedSet} (E : Algebra B) (F : Set (B 0)) : RankedSet :=
  fun n => Quot (@Equivalent B E F n)

def classMap {B : RankedSet} (E : Algebra B) (F : Set (B 0)) : RankedMap B (Carrier E F) :=
  fun _ => Quot.mk _

def Accepting {B : RankedSet} (E : Algebra B) (F : Set (B 0)) (a : Carrier E F 0) : Prop :=
  ∃ b, classMap E F 0 b = a ∧ b ∈ F

axiom algebra {B : RankedSet} (E : Algebra B) (F : Set (B 0)) :
    ∃ Q : Algebra (Carrier E F), ∀ n (S : System B n),
      Q.eval n (relabelSystem (classMap E F) S) = classMap E F n (E.eval n S)

axiom finite_carrier {B : RankedSet} (E : Algebra B) (F : Set (B 0))
    (hB : RankwiseFinite B) : RankwiseFinite (Carrier E F)

axiom accepting_class {B : RankedSet} (E : Algebra B) (F : Set (B 0)) (b : B 0) :
    Accepting E F (classMap E F 0 b) ↔ b ∈ F

axiom recognition {A B : RankedSet} (E : Algebra B) (F : Set (B 0))
    (Q : Algebra (Carrier E F))
    (hQ : ∀ n (S : System B n), Q.eval n (relabelSystem (classMap E F) S) = classMap E F n (E.eval n S))
    (η : RankedMap A B) (L : Language A) (hL : Recognizes E η F L) :
    Recognizes Q (fun n a => classMap E F n (η n a)) (Accepting E F) L

end Lax369799.PolynomialQuotient
