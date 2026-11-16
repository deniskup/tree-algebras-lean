import Lax369799.SupportedSystems
import Lax369799.Algebras

/-!
---
title: Algebras on fully supported systems
type: theorem
---
Evaluation is defined on the systems of Definition 6, with every output
reachable. Restriction of an algebra on arbitrary deterministic systems
preserves its algebra laws, unfolding invariance, and recognition. Evaluation commutes with surjective output renaming.
-/

namespace Lax369799.SupportedAlgebras
open RankedSystems (RankedSet RankedMap RankwiseFinite)
open SupportedSystems Morphisms

structure Algebra (A : RankedSet) where
  eval : ∀ n, System A n → A n
  isomorphic : ∀ n (S T : System A n), Isomorphic S.val.val T.val.val → eval n S = eval n T
  unit : ∀ n (a : A n), eval n (atomic a) = a
  associative : ∀ n (S : System (System A) n) (T : System A n),
    Flattening.SystemFlattening (forgetPattern S) T.val →
      eval n (relabel eval S) = eval n T

def UnfoldInvariant {A : RankedSet} (E : Algebra A) : Prop :=
  ∀ n (S T : System A n), UnfoldEquivalent S.val.val T.val.val → E.eval n S = E.eval n T

def Recognizes {A B : RankedSet} (E : Algebra B) (η : RankedMap A B)
    (F : Set (B 0)) (L : Algebras.Language A) : Prop :=
  ∀ T : System A 0, T.val ∈ L ↔ E.eval 0 (relabel η T) ∈ F

def Recognizable {A : RankedSet} (L : Algebras.Language A) : Prop :=
  ∃ (B : RankedSet) (E : Algebra B) (η : RankedMap A B) (F : Set (B 0)),
    RankwiseFinite B ∧ Recognizes E η F L

def restrict {A : RankedSet} (E : Algebras.Algebra A) : Algebra A where
  eval := fun n S => E.eval n S.val
  isomorphic := fun n S T h => E.isomorphic n S.val T.val h
  unit := E.unit
  associative := fun n S T h => E.associative n (forgetPattern S) T.val h

axiom restrict_invariant {A : RankedSet} (E : Algebras.Algebra A)
    (hE : Algebras.UnfoldInvariant E) : UnfoldInvariant (restrict E)

axiom legacy_recognizable {A : RankedSet} (L : Algebras.Language A)
    (hL : Algebras.Recognizable L) : Recognizable L

axiom rename_evaluation {A : RankedSet} (E : Algebra A)
    {m n : ℕ} (σ : Fin m → Fin n) (hσ : Function.Surjective σ) (S : System A m) :
    E.eval n (rename σ hσ S) = E.eval n (rename σ hσ (atomic (E.eval m S)))

end Lax369799.SupportedAlgebras

