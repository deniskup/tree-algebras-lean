import Lax369799.SyntacticOrder

/-!
---
title: Deterministic elements and the automaton property
type: definition
---
An element is deterministic if it is the value of a set-system using only
letters of ranks zero and one. Given a rank-zero element f, the automaton
property says that an element in an accepting context can be replaced by
a deterministic element below it while preserving acceptance above f.
This is the property used in Section 5.
-/

namespace Lax369799.AutomatonProperty
open RankedSystems Flattening SetAlgebras

def Deterministic {A : RankedSet} (E : SetAlgebra A) {n : ℕ} (a : A n) : Prop :=
  ∃ S : SetSystem A n, (∀ v, (S.graph.label v).1 ≤ 1) ∧ E.eval n S = a

def HasAutomatonProperty {A : RankedSet} (E : SetAlgebra A) (f : A 0) : Prop :=
  ∀ n (C : SetContext A n 0) (a : A n), Below E f (E.eval 0 (plug C (atomic a))) →
    ∃ δ : A n, Deterministic E δ ∧ Below E δ a ∧
      Below E f (E.eval 0 (plug C (atomic δ)))

def PlantInvariant {A : RankedSet} (E : SetAlgebra A) (f : A 0) : Prop :=
  ∀ S : SetSystem A 0, Below E f (E.eval 0 S) ↔ Below E f (E.eval 0 (plant S))

def OrderSeparating {A : RankedSet} (E : SetAlgebra A) (f : A 0) : Prop :=
  ∀ n (a b : A n),
    (∀ C : SetContext A n 0,
      Below E f (E.eval 0 (plug C (atomic a))) →
      Below E f (E.eval 0 (plug C (atomic b)))) → Below E a b

end Lax369799.AutomatonProperty
