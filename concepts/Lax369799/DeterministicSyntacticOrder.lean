import Lax369799.ContextRelabelling

/-!
---
title: Contextual equivalence of deterministic systems
type: theorem
---
Two systems are equivalent when every closed deterministic context gives
the same language-membership test. Recognition by a rankwise-finite algebra
makes this quotient rankwise finite, without requiring the recognizing
algebra itself to be unfolding-invariant. For an unfolding-invariant
language, equivalent unfoldings have the same contextual class.
-/
namespace Lax369799.DeterministicSyntacticOrder
open RankedSystems Flattening Algebras Morphisms

def Test {A : RankedSet} (L : Language A) {n : ℕ} (C : Context A n 0) (S : System A n) : Prop :=
  ∃ U : System A 0, U.val = plug C.val S.val ∧ U ∈ L

def Equivalent {A : RankedSet} (L : Language A) {n : ℕ} (S T : System A n) : Prop :=
  ∀ C : Context A n 0, Test L C S ↔ Test L C T

abbrev Carrier {A : RankedSet} (L : Language A) : RankedSet := fun n => Quot (@Equivalent A L n)

axiom value_refines {A B : RankedSet} (E : Algebra B) (η : RankedMap A B)
    (F : Set (B 0)) (L : Language A) (hL : Recognizes E η F L)
    {n : ℕ} (S T : System A n)
    (h : E.eval n (relabelSystem η S) = E.eval n (relabelSystem η T)) : Equivalent L S T

axiom unfold_refines {A : RankedSet} (L : Language A) (hL : UnfoldInvariantLanguage L)
    {n : ℕ} (S T : System A n) (h : UnfoldEquivalent S.val T.val) : Equivalent L S T

def AcceptingClass {A : RankedSet} (L : Language A) (a : Carrier L 0) : Prop :=
  ∃ S : System A 0, Quot.mk _ S = a ∧ S ∈ L

axiom closed_membership {A : RankedSet} (L : Language A) (hL : UnfoldInvariantLanguage L)
    (S T : System A 0) (h : Equivalent L S T) : S ∈ L ↔ T ∈ L

axiom accepting_class {A : RankedSet} (L : Language A) (hL : UnfoldInvariantLanguage L)
    (S : System A 0) : AcceptingClass L (Quot.mk _ S) ↔ S ∈ L

axiom finite_carrier {A : RankedSet} (L : Language A) (hL : Recognizable L) : RankwiseFinite (Carrier L)

end Lax369799.DeterministicSyntacticOrder
