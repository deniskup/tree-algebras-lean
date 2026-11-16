import Lax369799.FiniteVertexReplacement
import Lax369799Proofs.ExpandedSyntacticAlgebra

namespace Lax369799Proofs.FiniteVertexReplacement
open Lax369799.RankedSystems (RankedSet)
open Lax369799.FinitePresentations Lax369799.FiniteContexts Lax369799.FiniteContextualOrder
open Lax369799.FiniteAcceptance Lax369799.FiniteSyntacticAlgebra Lax369799.ExpandedSyntacticAlgebra

/--
---
conclusion: Lax369799.FiniteVertexReplacement.vertex_context
---
Drill the selected vertex and expand the atomic labels at the others.
The inner unit isomorphism identifies filling with relabelling.
-/
theorem vertex_context {A B : RankedSet} {n : ℕ} (P : FiniteSystem B n)
    (q : ∀ v : P.Vertex, A (P.graph.label v).1) (v : P.Vertex) :
    ∃ C : Context A (P.graph.label v).1 n,
      ∀ r : ∀ w : P.Vertex, A (P.graph.label w).1,
        (∀ w, w ≠ v → q w = r w) →
        Isomorphic (plug C (atomic (r v))) (withLabels P r) := by
  obtain ⟨C, hc⟩ := FiniteContexts.extension (fun _ a => a)
    (FiniteContextualOrder.drill P (fun w => atomic (q w)) v)
  refine ⟨C, ?_⟩
  intro r hr
  have h := hc (atomic (r v))
  rw [FiniteContextualOrder.interpret_drill P (fun w => atomic (q w))
    (fun w => atomic (r w)) v (fun w hw => congrArg atomic (hr w hw))] at h
  obtain ⟨f⟩ := h
  obtain ⟨g⟩ := UntrimmedFlattening.inner_atomic (withLabels P r)
  exact ⟨UntrimmedFlattening.isoTrans f g⟩

/--
---
conclusion: Lax369799.FiniteVertexReplacement.simultaneous_replacement
---
Process the finite vertex set one vertex at a time. At each stage the
current labels outside the selected vertex form its testing context.
-/
theorem simultaneous_replacement {A B : RankedSet} (L : Lax369799.Algebras.Language A)
    (hL : Lax369799.Algebras.UnfoldInvariantLanguage L) (hrec : Lax369799.Algebras.Recognizable L)
    (E : SyntacticAlgebra L) (P : FiniteSystem B 0)
    (q : ∀ v : P.Vertex, Carrier (Accepting L) (P.graph.label v).1)
    (hq : AcceptingClass (Accepting L) (E.algebra.eval 0 (withLabels P q))) :
    ∃ r : ∀ v : P.Vertex, Carrier (Accepting L) (P.graph.label v).1,
      (∀ v, Lax369799.FiniteExtremal.Deterministic E.algebra (r v) ∧ ClassBelow (Accepting L) (r v) (q v)) ∧
      AcceptingClass (Accepting L) (E.algebra.eval 0 (withLabels P r)) := by
  classical
  have step (s : Finset P.Vertex) :
      ∃ r : ∀ v : P.Vertex, Carrier (Accepting L) (P.graph.label v).1,
        (∀ v ∈ s, Lax369799.FiniteExtremal.Deterministic E.algebra (r v) ∧ ClassBelow (Accepting L) (r v) (q v)) ∧
        (∀ v, v ∉ s → r v = q v) ∧
        AcceptingClass (Accepting L) (E.algebra.eval 0 (withLabels P r)) := by
    induction s using Finset.induction_on with
    | empty => exact ⟨q, by simp, by simp, hq⟩
    | @insert v s hv ih =>
      obtain ⟨r, hr, he, ha⟩ := ih
      obtain ⟨C, hc⟩ := vertex_context P r v
      have hvacc : AcceptingClass (Accepting L) (E.algebra.eval 0 (plug C (atomic (r v)))) := by
        rw [E.algebra.isomorphic _ _ _ (hc r (fun _ _ => rfl))]
        exact ha
      obtain ⟨d, hd, hle, hdacc⟩ := ExpandedSyntacticAlgebra.automaton_property L hL hrec E C (r v) hvacc
      let r' := Function.update r v d
      have heq : ∀ w, w ≠ v → r w = r' w := by
        intro w hw
        simp [r', hw]
      refine ⟨r', ?_, ?_, ?_⟩
      · intro w hw
        rcases Finset.mem_insert.mp hw with rfl | hw
        · simpa [r', he w hv] using And.intro hd hle
        · rw [← heq w (by intro h; subst w; exact hv hw)]
          exact hr w hw
      · intro w hw
        have hws : w ∉ s := fun h => hw (Finset.mem_insert_of_mem h)
        have hwv : w ≠ v := fun h => hw (Finset.mem_insert.mpr (Or.inl h))
        rw [← heq w hwv]
        exact he w hws
      · have hi := E.algebra.isomorphic _ _ _ (hc r' heq)
        have hvd : r' v = d := by simp [r']
        rw [hvd] at hi
        rw [← hi]
        exact hdacc
  obtain ⟨r, hr, _, ha⟩ := step Finset.univ
  exact ⟨r, fun v => hr v (Finset.mem_univ v), ha⟩

end Lax369799Proofs.FiniteVertexReplacement
