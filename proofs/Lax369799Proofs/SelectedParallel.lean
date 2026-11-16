import Lax369799.SelectedParallel
import Lax369799Proofs.SelectedChoicePreservation
import Lax369799Proofs.FiniteVertexReplacement

namespace Lax369799Proofs.SelectedParallel
open Lax369799
open RankedSystems (RankedSet)
open FinitePresentations FiniteContexts FiniteContextualOrder FiniteAcceptance
open FiniteSyntacticAlgebra ExpandedSyntacticAlgebra

private theorem refine_tuple {A : RankedSet} (L : Algebras.Language A)
    (hL : Algebras.UnfoldInvariantLanguage L) (hrec : Algebras.Recognizable L)
    (E : SyntacticAlgebra L) {k : ℕ}
    (C : Context (Carrier (Accepting L)) k 0) (b : Fin k → Carrier (Accepting L) 1)
    (hb : AcceptingClass (Accepting L) (E.algebra.eval 0 (plug C
      (atomic (E.algebra.eval k (ofSetSystem (DeterministicElements.parallel b))))))) :
    ∃ r : Fin k → Carrier (Accepting L) 1,
      (∀ i, ExtremalUnaryTypes.Selected L E (r i) ∧ ClassBelow (Accepting L) (r i) (b i)) ∧
      AcceptingClass (Accepting L) (E.algebra.eval 0 (plug C
        (atomic (E.algebra.eval k (ofSetSystem (DeterministicElements.parallel r)))))) := by
  classical
  let par (r : Fin k → Carrier (Accepting L) 1) :=
    ofSetSystem (DeterministicElements.parallel r)
  have step (s : Finset (Fin k)) :
      ∃ r : Fin k → Carrier (Accepting L) 1,
        (∀ i ∈ s, ExtremalUnaryTypes.Selected L E (r i) ∧ ClassBelow (Accepting L) (r i) (b i)) ∧
        (∀ i, i ∉ s → r i = b i) ∧
        AcceptingClass (Accepting L) (E.algebra.eval 0 (plug C (atomic (E.algebra.eval k (par r))))) := by
    induction s using Finset.induction_on with
    | empty => exact ⟨b, by simp, by simp, hb⟩
    | @insert i s hi ih =>
      obtain ⟨r, hr, he, ha⟩ := ih
      obtain ⟨H, hH⟩ := FiniteVertexReplacement.vertex_context (par r) (fun v => r v) i
      obtain ⟨K, _, hK⟩ := FiniteContexts.composition C H
      have htest (u : Fin k → Carrier (Accepting L) 1) (hu : ∀ j, j ≠ i → r j = u j) :
          E.algebra.eval 0 (plug K (atomic (u i))) =
            E.algebra.eval 0 (plug C (atomic (E.algebra.eval k (par u)))) := by
        rw [E.algebra.isomorphic _ _ _ (hK (atomic (u i))), FiniteEvaluation.context_evaluation]
        have hh := E.algebra.isomorphic _ _ _ (hH u hu)
        change E.algebra.eval k (plug H (atomic (u i))) = E.algebra.eval k (par u) at hh
        rw [hh]
      have hai : AcceptingClass (Accepting L) (E.algebra.eval 0 (plug K (atomic (r i)))) := by
        rw [htest r (fun _ _ => rfl)]
        exact ha
      obtain ⟨d, hd, hle, hda⟩ := ExtremalUnaryTypes.replacement L hL hrec E K (r i) hai
      let u := Function.update r i d
      have heu : ∀ j, j ≠ i → r j = u j := by intro j hj; simp [u, hj]
      refine ⟨u, ?_, ?_, ?_⟩
      · intro j hj
        rcases Finset.mem_insert.mp hj with rfl | hj
        · simpa [u, he j hi] using And.intro hd hle
        · rw [← heu j (by intro h; subst j; exact hi hj)]
          exact hr j hj
      · intro j hj
        have hji : j ≠ i := fun h => hj (Finset.mem_insert.mpr (Or.inl h))
        rw [← heu j hji]
        exact he j (fun h => hj (Finset.mem_insert_of_mem h))
      · have ht := htest u heu
        have hui : u i = d := by simp [u]
        rw [hui] at ht
        rwa [← ht]
  obtain ⟨r, hr, _, ha⟩ := step Finset.univ
  exact ⟨r, fun i => hr i (Finset.mem_univ i), ha⟩

/--
---
conclusion: Lax369799.SelectedParallel.accepting_parallel
---
First choose a parallel witness. Refine each unary component in its
composed testing context. Monotonicity retains the transition bound.
-/
theorem accepting_parallel {A : RankedSet} (L : Algebras.Language A)
    (hL : Algebras.UnfoldInvariantLanguage L) (hrec : Algebras.Recognizable L)
    (E : SyntacticAlgebra L) {k : ℕ} (hk : 1 ≤ k)
    (C : Context (Carrier (Accepting L)) k 0) (a : Carrier (Accepting L) k)
    (ha : AcceptingClass (Accepting L) (E.algebra.eval 0 (plug C (atomic a)))) :
    ∃ b : Fin k → Carrier (Accepting L) 1,
      (∀ i, ExtremalUnaryTypes.Selected L E (b i)) ∧
      ClassBelow (Accepting L) (E.algebra.eval k (ofSetSystem (DeterministicElements.parallel b))) a ∧
      AcceptingClass (Accepting L) (E.algebra.eval 0 (plug C
        (atomic (E.algebra.eval k (ofSetSystem (DeterministicElements.parallel b)))))) := by
  obtain ⟨b, hba, hb⟩ := ParallelReplacement.accepting_parallel L hL hrec E hk C a ha
  obtain ⟨r, hr, hacc⟩ := refine_tuple L hL hrec E C b hb
  refine ⟨r, fun i => (hr i).1, ?_, hacc⟩
  have hle := FiniteSyntacticAlgebra.evaluation_monotone (Accepting L)
    (FiniteAcceptance.accepting_isomorphic L) E.algebra E.evaluates
    (ofSetSystem (DeterministicElements.parallel b)) (fun i => r i) (fun i => b i)
    (fun i => (hr i).2)
  exact (FiniteContextualOrder.class_order (Accepting L) k).2.2 _ _ _ hle hba

end Lax369799Proofs.SelectedParallel
