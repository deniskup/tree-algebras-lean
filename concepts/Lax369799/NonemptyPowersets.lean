import Lax369799.PolynomialContexts
import Mathlib.Data.Fintype.Powerset

/-!
---
title: Nonempty powerset algebras
type: theorem
---
The nonempty subsets of each sort form an algebra by choosing one allowed
label at each vertex and collecting all resulting evaluations. Nonemptiness
allows arbitrary choices at components removed by reachable restriction.
This construction is used for projections that forget extra vertex marks.
-/
namespace Lax369799.NonemptyPowersets
open RankedSystems Algebras PolynomialContexts

abbrev Carrier (B : RankedSet) : RankedSet := fun n => {s : Set (B n) // s.Nonempty}

def values {B : RankedSet} (E : Algebra B) {n : ℕ} (S : System (Carrier B) n) : Set (B n) :=
  {b | ∃ q : ∀ v, B (S.val.graph.label v).1,
    (∀ v, q v ∈ (S.val.graph.label v).2.val) ∧ E.eval n (withLabels S q) = b}

noncomputable def evaluate {B : RankedSet} (E : Algebra B) (n : ℕ)
    (S : System (Carrier B) n) : Carrier B n :=
  ⟨values E S, by
    let q := fun v => Classical.choose (S.val.graph.label v).2.property
    exact ⟨E.eval n (withLabels S q), q,
      fun v => Classical.choose_spec (S.val.graph.label v).2.property, rfl⟩⟩

axiom algebra {B : RankedSet} (E : Algebra B) :
    ∃ F : Algebra (Carrier B), F.eval = evaluate E

axiom finite_carrier {B : RankedSet} (hB : RankwiseFinite B) : RankwiseFinite (Carrier B)

end Lax369799.NonemptyPowersets
