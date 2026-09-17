import Lax369799.Morphisms
import Lax369799.Flattening

/-!
---
title: Algebras and recognition
type: definition
---
An algebra evaluates systems over its own ranked carrier. Evaluation is
invariant under isomorphism, evaluates atomic systems as their labels, and
commutes with flattening. The explicit isomorphism clause accounts for our
enumeration of finite vertex sets. A regular-tree algebra also identifies
unfold-equivalent systems. A recognising map assigns an algebra element to
each letter; a set of elements of sort zero specifies acceptance.
See Section 3.
-/

namespace Lax369799.Algebras
open RankedSystems Morphisms Flattening

structure Algebra (A : RankedSet) where
  eval : ∀ n, System A n → A n
  isomorphic : ∀ n (S T : System A n), Isomorphic S.val T.val → eval n S = eval n T
  unit : ∀ n (a : A n), eval n (atomicSystem a) = a
  associative : ∀ n (S : System (System A) n) (T : System A n),
    SystemFlattening S T → eval n (relabelSystem eval S) = eval n T

def UnfoldInvariant {A : RankedSet} (E : Algebra A) : Prop :=
  ∀ n (S T : System A n), UnfoldEquivalent S.val T.val → E.eval n S = E.eval n T

abbrev Language (A : RankedSet) := Set (System A 0)

def UnfoldInvariantLanguage {A : RankedSet} (L : Language A) : Prop :=
  ∀ S T, UnfoldEquivalent S.val T.val → (S ∈ L ↔ T ∈ L)

def Recognizes {A B : RankedSet} (E : Algebra B) (η : RankedMap A B)
    (F : Set (B 0)) (L : Language A) : Prop :=
  ∀ T, T ∈ L ↔ E.eval 0 (relabelSystem η T) ∈ F

def Recognizable {A : RankedSet} (L : Language A) : Prop :=
  ∃ (B : RankedSet) (E : Algebra B) (η : RankedMap A B) (F : Set (B 0)),
    RankwiseFinite B ∧ Recognizes E η F L

def RegularTreeRecognizable {A : RankedSet} (L : Language A) : Prop :=
  ∃ (B : RankedSet) (E : Algebra B) (η : RankedMap A B) (F : Set (B 0)),
    RankwiseFinite B ∧ UnfoldInvariant E ∧ Recognizes E η F L

structure AlgebraMorphism {A B : RankedSet} (E : Algebra A) (F : Algebra B) where
  map : RankedMap A B
  commutes : ∀ n (S : System A n), F.eval n (relabelSystem map S) = map n (E.eval n S)

end Lax369799.Algebras
