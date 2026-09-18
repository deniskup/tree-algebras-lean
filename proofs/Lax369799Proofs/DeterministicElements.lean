import Lax369799.DeterministicElements
import Lax369799Proofs.UnarySystems
import Lax369799Proofs.SetAlgebraTheorems

set_option backward.isDefEq.respectTransparency false
namespace Lax369799Proofs.DeterministicElements
open Lax369799.RankedSystems Lax369799.Morphisms Lax369799.SetAlgebras
open Lax369799.AutomatonProperty Lax369799.DeterministicElements Lax369799.UnarySystems
open Lax369799.PresentationCovers Lax369799Proofs.Pullbacks

private def piecesCover {A : RankedSet} {n : ℕ} (S : SetSystem A n) :
    Cover (Flattening.graph (parallel (projection S))) (variablePieces S.graph) where
  toFun := fun v => (v.1, v.2)
  label := fun _ => rfl
  initial := fun _ h => h.2
  root := by
    intro v h
    rcases h with h | ⟨h, _⟩
    · exact h
    · exact False.elim h
  edge := by
    intro v d t ht
    rcases ht with ⟨w, hw, rfl⟩ | ⟨i, hi, ht⟩
    · exact ⟨.inl w, hw, (by intro i h; cases h), rfl⟩
    · rcases ht with ⟨w, ⟨_, he⟩, _, _⟩ | ⟨j, ⟨_, he⟩, rfl⟩
      · cases he
      · have hj : j = v.1 := Sum.inr.inj he
        subst j
        exact ⟨.inr v.1, hi, fun _ h => (Sum.inr.inj h).symm, rfl⟩
  initial_lift := fun v h => ⟨⟨v.1, v.2⟩, ⟨trivial, h⟩, rfl⟩
  root_lift := fun v h => ⟨⟨v.1, v.2⟩, Or.inl h, rfl⟩
  edge_lift := by
    rintro v d t ⟨s, hs, hv, rfl⟩
    cases s with
    | inl w => exact ⟨.inl ⟨v.1, w⟩, Or.inl ⟨w, hs, rfl⟩, rfl⟩
    | inr j =>
      have hj := hv j rfl
      subst j
      exact ⟨.inr v.1, Or.inr ⟨(0 : Fin 1), hs, Or.inr ⟨v.1, ⟨rfl, rfl⟩, rfl⟩⟩, rfl⟩

private theorem eval_yields {A : RankedSet} (E : SetAlgebra A) {n : ℕ}
    (S T : SetSystem A n) (h : YieldEquivalent S T) : E.eval n S = E.eval n T :=
  (SetAlgebraTheorems.order_laws E n).2.1 _ _
    (SetAlgebraTheorems.yield_order E T S (fun U => (h U).mpr))
    (SetAlgebraTheorems.yield_order E S T (fun U => (h U).mp))

private theorem normal_value {A : RankedSet} (E : SetAlgebra A) {n : ℕ} (hn : 0 < n)
    (S : SetSystem A n) (hS : ∀ v, (S.graph.label v).1 ≤ 1) :
    E.eval n (parallel (fun i => E.eval 1 (projection S i))) = E.eval n S := by
  have hpieces := UnarySystems.variable_decomposition hn S.graph hS
  let c := piecesCover S
  let m : Map _ _ := ⟨c.toFun, c.initial, c.root, c.label, c.edge⟩
  have hm := trimMap_surjective m c.initial_lift c.root_lift c.edge_lift
  have hy := (Yields.morphism_yields (trimMap m)).2 hm
  let p := FiniteAcceptance.trimProjection S.graph
  let f : Morphism (trim S.graph) S := ⟨p.toFun, p.initial, p.root, p.label, p.edge⟩
  have hf : f.LocallySurjective := ⟨p.initial_lift, p.root_lift, p.edge_lift⟩
  have ht := (Yields.morphism_yields f).2 hf
  have he : YieldEquivalent (Lax369799.Flattening.flatten (parallel (projection S))) S :=
    fun U => (hy U).trans ((hpieces U).symm.trans (ht U))
  calc
    E.eval n (parallel (fun i => E.eval 1 (projection S i))) =
        E.eval n (Lax369799.Flattening.flatten (parallel (projection S))) :=
      E.associative n (parallel (projection S))
    _ = E.eval n S := eval_yields E _ _ he

/--
---
conclusion: Lax369799.DeterministicElements.unary_normal_form
---
Restrict to each variable and evaluate the resulting unary presentation.
Their parallel substitution has the same yields as the original unary
presentation. Continuity and the induced order identify their evaluations.
-/
theorem unary_normal_form {A : RankedSet} (E : SetAlgebra A) {n : ℕ} (hn : 0 < n)
    (a : A n) : Deterministic E a ↔ ∃ b : Fin n → A 1, E.eval n (parallel b) = a := by
  constructor
  · rintro ⟨S, hS, he⟩
    exact ⟨fun i => E.eval 1 (projection S i), (normal_value E hn S hS).trans he⟩
  · rintro ⟨b, hb⟩
    exact ⟨parallel b, fun _ => Nat.le_refl 1, hb⟩

end Lax369799Proofs.DeterministicElements
