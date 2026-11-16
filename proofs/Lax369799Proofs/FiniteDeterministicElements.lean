import Lax369799.FiniteDeterministicElements

namespace Lax369799Proofs.FiniteDeterministicElements
open Lax369799.RankedSystems (RankedSet)
open Lax369799.FinitePresentations Lax369799.FiniteSyntacticAlgebra Lax369799.FiniteExtremal

/--
---
conclusion: Lax369799.FiniteDeterministicElements.realization
---
Each flattened vertex belongs to a chosen generating presentation, so its
label still has rank at most one. Associativity gives the evaluation law.
-/
theorem realization {A B : RankedSet} (E : Algebra A) {n : ℕ} (P : FiniteSystem B n)
    (q : ∀ v : P.Vertex, A (P.graph.label v).1) (hq : ∀ v, Deterministic E (q v)) :
    ∃ D : ∀ v : P.Vertex, FiniteSystem A (P.graph.label v).1,
      (∀ v, (∀ w, ((D v).graph.label w).1 ≤ 1) ∧ E.eval _ (D v) = q v) ∧
      (∀ w, ((flatten (withLabels P D)).graph.label w).1 ≤ 1) ∧
      E.eval n (flatten (withLabels P D)) = E.eval n (withLabels P q) := by
  classical
  choose D hD he using hq
  refine ⟨D, fun v => ⟨hD v, he v⟩, ?_, ?_⟩
  · intro w
    let u := (Fintype.equivFin ((v : P.Vertex) × (D v).Vertex)).symm w
    exact hD u.1 u.2
  · have hr : relabel E.eval (withLabels P D) = withLabels P q := by
      dsimp only [relabel, withLabels]
      congr 1
      congr 1
      funext v
      exact congrArg (Sigma.mk (P.graph.label v).1) (he v)
    exact (E.associative n (withLabels P D)).symm.trans (congrArg (E.eval n) hr)

/--
---
conclusion: Lax369799.FiniteDeterministicElements.substitution_closed
---
The flattened generating presentations witness determinism of the value.
-/
theorem substitution_closed {A B : RankedSet} (E : Algebra A) {n : ℕ} (P : FiniteSystem B n)
    (q : ∀ v : P.Vertex, A (P.graph.label v).1) (hq : ∀ v, Deterministic E (q v)) :
    Deterministic E (E.eval n (withLabels P q)) := by
  obtain ⟨D, _, hD, he⟩ := realization E P q hq
  exact ⟨flatten (withLabels P D), hD, he⟩

end Lax369799Proofs.FiniteDeterministicElements
