import Lax369799.FiniteLocalReplacement
import Lax369799Proofs.FiniteVertexReplacement

namespace Lax369799Proofs.FiniteLocalReplacement
open Lax369799.RankedSystems (RankedSet)
open Lax369799.FinitePresentations Lax369799.FiniteContexts Lax369799.FiniteSyntacticAlgebra

/--
---
conclusion: Lax369799.FiniteLocalReplacement.simultaneous
---
Replace the vertices in a finite-set induction. The current labels supply
the surrounding context and untouched labels retain their original values.
-/
theorem simultaneous {A B : RankedSet} (E : Algebra A) (F : Set (A 0))
    (G : ∀ n, A n → A n → Prop)
    (hG : ∀ k (C : Context A k 0) (a : A k), E.eval 0 (plug C (atomic a)) ∈ F →
      ∃ b, G k a b ∧ E.eval 0 (plug C (atomic b)) ∈ F)
    (P : FiniteSystem B 0) (q : ∀ v : P.Vertex, A (P.graph.label v).1)
    (hq : E.eval 0 (withLabels P q) ∈ F) :
    ∃ r : ∀ v : P.Vertex, A (P.graph.label v).1,
      (∀ v, G _ (q v) (r v)) ∧ E.eval 0 (withLabels P r) ∈ F := by
  classical
  have step (s : Finset P.Vertex) :
      ∃ r : ∀ v : P.Vertex, A (P.graph.label v).1,
        (∀ v ∈ s, G _ (q v) (r v)) ∧
        (∀ v, v ∉ s → r v = q v) ∧
        E.eval 0 (withLabels P r) ∈ F := by
    induction s using Finset.induction_on with
    | empty => exact ⟨q, by simp, by simp, hq⟩
    | @insert v s hv ih =>
      obtain ⟨r, hr, he, ha⟩ := ih
      obtain ⟨C, hc⟩ := FiniteVertexReplacement.vertex_context P r v
      have hvacc : E.eval 0 (plug C (atomic (r v))) ∈ F := by
        rw [E.isomorphic _ _ _ (hc r (fun _ _ => rfl))]
        exact ha
      obtain ⟨d, hd, hdacc⟩ := hG _ C (r v) hvacc
      let r' := Function.update r v d
      have heq : ∀ w, w ≠ v → r w = r' w := by
        intro w hw
        simp [r', hw]
      refine ⟨r', ?_, ?_, ?_⟩
      · intro w hw
        rcases Finset.mem_insert.mp hw with rfl | hw
        · simpa [r', he w hv] using hd
        · rw [← heq w (by intro h; subst w; exact hv hw)]
          exact hr w hw
      · intro w hw
        have hws : w ∉ s := fun h => hw (Finset.mem_insert_of_mem h)
        have hwv : w ≠ v := fun h => hw (Finset.mem_insert.mpr (Or.inl h))
        rw [← heq w hwv]
        exact he w hws
      · have hi := E.isomorphic _ _ _ (hc r' heq)
        have hvd : r' v = d := by simp [r']
        rw [hvd] at hi
        rw [← hi]
        exact hdacc
  obtain ⟨r, hr, _, ha⟩ := step Finset.univ
  exact ⟨r, fun v => hr v (Finset.mem_univ v), ha⟩

end Lax369799Proofs.FiniteLocalReplacement
