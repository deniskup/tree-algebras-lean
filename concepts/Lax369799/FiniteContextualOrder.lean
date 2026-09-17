import Lax369799.FiniteContexts

/-!
---
title: Contextual preorders on finite presentations
type: theorem
---
For an isomorphism-invariant property of closed finite presentations,
comparison by all one-hole contexts is preserved by substitution.
This construction does not assume a continuity axiom for algebra values.
-/

namespace Lax369799.FiniteContextualOrder
open RankedSystems (RankedSet)
open FinitePresentations FiniteContexts

abbrev ClosedProperty (A : RankedSet) := Set (FiniteSystem A 0)

def IsoInvariant {A : RankedSet} (F : ClosedProperty A) : Prop :=
  ∀ S T, Isomorphic S T → (S ∈ F ↔ T ∈ F)

def Below {A : RankedSet} (F : ClosedProperty A) {n : ℕ}
    (S T : FiniteSystem A n) : Prop :=
  ∀ C : Context A n 0, plug C S ∈ F → plug C T ∈ F

def Equivalent {A : RankedSet} (F : ClosedProperty A) {n : ℕ}
    (S T : FiniteSystem A n) : Prop := Below F S T ∧ Below F T S

abbrev Carrier {A : RankedSet} (F : ClosedProperty A) : RankedSet :=
  fun n => Quot (@Equivalent A F n)

def quotientMap {A : RankedSet} (F : ClosedProperty A) :
    RankedSystems.RankedMap (FiniteSystem A) (Carrier F) := fun _ => Quot.mk _

axiom contextual_congruence {A : RankedSet} (F : ClosedProperty A) (hF : IsoInvariant F)
    {k n : ℕ} (C : Context A k n) (S T : FiniteSystem A k) (h : Below F S T) :
    Below F (plug C S) (plug C T)

axiom contextual_acceptance {A : RankedSet} (F : ClosedProperty A) (hF : IsoInvariant F)
    (S T : FiniteSystem A 0) (h : Below F S T) : S ∈ F → T ∈ F

axiom contextual_iso {A : RankedSet} (F : ClosedProperty A) (hF : IsoInvariant F)
    {n : ℕ} (S T : FiniteSystem A n) (h : Isomorphic S T) : Equivalent F S T

axiom flatten_monotone {A B : RankedSet} (F : ClosedProperty A) (hF : IsoInvariant F)
    {n : ℕ} (P : FiniteSystem B n)
    (q r : ∀ v : P.Vertex, FiniteSystem A (P.graph.label v).1)
    (h : ∀ v, Below F (q v) (r v)) :
    Below F (flatten (withLabels P q)) (flatten (withLabels P r))

end Lax369799.FiniteContextualOrder
