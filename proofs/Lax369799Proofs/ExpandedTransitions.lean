import Lax369799.ExpandedTransitions
import Lax369799Proofs.SelectedParallel
import Lax369799Proofs.ExpandedCertificates
import Lax369799Proofs.FiniteLocalReplacement

namespace Lax369799Proofs.ExpandedTransitions
open Lax369799.RankedSystems (RankedSet System)
open Lax369799.FinitePresentations Lax369799.FiniteContextualOrder Lax369799.FiniteAcceptance
open Lax369799.FiniteSyntacticAlgebra Lax369799.ExpandedSyntacticAlgebra Lax369799.UnfoldAutomata
open Lax369799.ExpandedTransitions

/--
---
conclusion: Lax369799.ExpandedTransitions.accepting_transition
---
Encode the parallel tuple supplied by the split extremal witness as finite
unary types. No original set-algebra continuity axiom is used.
-/
theorem accepting_transition {A : RankedSet} (L : Lax369799.Algebras.Language A)
    (hL : Lax369799.Algebras.UnfoldInvariantLanguage L) (hrec : Lax369799.Algebras.Recognizable L)
    [Fintype (Carrier (Accepting L) 1)] [Fintype (Carrier (Accepting L) 0)]
    (E : SyntacticAlgebra L)
    (D : WordCondition (Fintype.card (Carrier (Accepting L) 1))
      (Fintype.card (Carrier (Accepting L) 0)))
    (n : ℕ) (a : A (n + 1)) (C : Lax369799.FiniteContexts.Context (Carrier (Accepting L)) (n + 1) 0)
    (ha : AcceptingClass (Accepting L) (E.algebra.eval 0 (Lax369799.FiniteContexts.plug C
      (atomic (quotientMap (Accepting L) _ (atomic a)))))) :
    ∃ b ∈ (automaton L E D).transition n a,
      AcceptingClass (Accepting L) (E.algebra.eval 0 (Lax369799.FiniteContexts.plug C
        (atomic (E.algebra.eval (n + 1) (ofSetSystem
          (Lax369799.DeterministicElements.parallel (Lax369799.AlgebraicTransitions.decodeTypes b))))))) := by
  obtain ⟨b, hs, hb, ha⟩ := SelectedParallel.accepting_parallel L hL hrec E (by omega) C _ ha
  let t := fun i => (Fintype.equivFin (Carrier (Accepting L) 1)) (b i)
  have ht : Lax369799.AlgebraicTransitions.decodeTypes t = b := by
    funext i
    exact (Fintype.equivFin _).symm_apply_apply _
  refine ⟨t, ?_, ?_⟩
  · change (∀ i, Lax369799.ExtremalUnaryTypes.Selected L E
      (Lax369799.AlgebraicTransitions.decodeTypes t i)) ∧ ClassBelow _
      (E.algebra.eval _ (ofSetSystem (Lax369799.DeterministicElements.parallel
        (Lax369799.AlgebraicTransitions.decodeTypes t)))) _
    rw [ht]
    exact ⟨hs, hb⟩
  · rw [ht]
    exact ha

private theorem input_cast {A : RankedSet} (L : Lax369799.Algebras.Language A)
    {n m : ℕ} (h : n = m) (a : A n) :
    (h.symm ▸ quotientMap (Accepting L) m (atomic (h ▸ a)) : Carrier (Accepting L) n) = quotientMap (Accepting L) n (atomic a) := by
  cases h
  rfl

private theorem transition_cast {A : RankedSet} (L : Lax369799.Algebras.Language A)
    (E : SyntacticAlgebra L) {k l : ℕ} (h : k = l) (a : A k)
    (b : Fin k → Carrier (Accepting L) 1)
    (hb : ClassBelow (Accepting L)
      (E.algebra.eval l (ofSetSystem (Lax369799.DeterministicElements.parallel
        (fun i => b (Fin.cast h.symm i)))))
      (quotientMap (Accepting L) l (atomic (h ▸ a)))) :
    ClassBelow (Accepting L)
      (E.algebra.eval k (ofSetSystem (Lax369799.DeterministicElements.parallel b)))
      (quotientMap (Accepting L) k (atomic a)) := by
  cases h
  exact hb

/--
---
conclusion: Lax369799.ExpandedTransitions.run_label_below
---
Internal transitions specify the contextual inequality. Leaf transitions
specify the exact value of the original nullary letter.
-/
theorem run_label_below {A : RankedSet} (L : Lax369799.Algebras.Language A)
    [Fintype (Carrier (Accepting L) 1)] [Fintype (Carrier (Accepting L) 0)]
    (E : SyntacticAlgebra L)
    (D : WordCondition (Fintype.card (Carrier (Accepting L) 1))
      (Fintype.card (Carrier (Accepting L) 0)))
    {S : System A 0} (r : Run (automaton L E D) S) (v : S.val.Vertex) :
    ClassBelow (Accepting L) (runLabel L E D r.toLabelling v)
      (quotientMap (Accepting L) _ (atomic (S.val.graph.label v).2)) := by
  unfold runLabel
  dsimp only [Run.toLabelling]
  split_ifs with h
  · have hl := r.leaves v h
    change r.leafType v h = (Fintype.equivFin (Carrier (Accepting L) 0))
      (quotientMap (Accepting L) _ (atomic (h ▸ (S.val.graph.label v).2))) at hl
    rw [hl, Equiv.symm_apply_apply]
    rw [input_cast L h]
    exact (FiniteContextualOrder.class_order _ _).1 _
  · obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero h
    have ht := (r.transitions v n hn).2
    change ClassBelow _ (E.algebra.eval _ (ofSetSystem (Lax369799.DeterministicElements.parallel
      (Lax369799.AlgebraicTransitions.decodeTypes (fun i => r.edgeType v (Fin.cast hn.symm i))))))
      (quotientMap (Accepting L) _ (atomic (hn ▸ (S.val.graph.label v).2))) at ht
    exact transition_cast L E hn (S.val.graph.label v).2
      (fun i => (Fintype.equivFin (Carrier (Accepting L) 1)).symm (r.edgeType v i)) ht

/--
---
conclusion: Lax369799.ExpandedTransitions.evaluated_run_sound
---
Evaluation is monotone in the vertex labels. Acceptance is upward closed,
and the canonical input labels evaluate to the input's contextual class.
-/
theorem evaluated_run_sound {A : RankedSet} (L : Lax369799.Algebras.Language A)
    (hL : Lax369799.Algebras.UnfoldInvariantLanguage L)
    [Fintype (Carrier (Accepting L) 1)] [Fintype (Carrier (Accepting L) 0)]
    (E : SyntacticAlgebra L)
    (D : WordCondition (Fintype.card (Carrier (Accepting L) 1))
      (Fintype.card (Carrier (Accepting L) 0)))
    {S : System A 0} (r : Run (automaton L E D) S)
    (hr : AcceptingClass (Accepting L)
      (E.algebra.eval 0 (withLabels (ofSetSystem S.val) (runLabel L E D r.toLabelling)))) : S ∈ L := by
  have hm := FiniteSyntacticAlgebra.evaluation_monotone (Accepting L)
    (FiniteAcceptance.accepting_isomorphic L) E.algebra E.evaluates (ofSetSystem S.val)
    (runLabel L E D r.toLabelling) (fun v => quotientMap (Accepting L) _ (atomic (S.val.graph.label v).2))
    (run_label_below L E D r)
  have ha := (FiniteSyntacticAlgebra.accepting_classes (Accepting L)
    (FiniteAcceptance.accepting_isomorphic L)).2 _ _ hr hm
  change AcceptingClass (Accepting L) (E.algebra.eval 0
    (relabel (fun k a => quotientMap (Accepting L) k (atomic a)) (ofSetSystem S.val))) at ha
  rw [ExpandedCertificates.input_evaluation L E] at ha
  exact (ExpandedSyntacticAlgebra.recognition L hL S).mp ha

private theorem transition_cast_back {A : RankedSet} (L : Lax369799.Algebras.Language A)
    (E : SyntacticAlgebra L) {k l : ℕ} (h : k = l) (a : A k)
    (b : Fin k → Carrier (Accepting L) 1)
    (hb : ClassBelow (Accepting L)
      (E.algebra.eval k (ofSetSystem (Lax369799.DeterministicElements.parallel b)))
      (quotientMap (Accepting L) k (atomic a))) :
    ClassBelow (Accepting L)
      (E.algebra.eval l (ofSetSystem (Lax369799.DeterministicElements.parallel
        (fun i => b (Fin.cast h.symm i)))))
      (quotientMap (Accepting L) l (atomic (h ▸ a))) := by
  cases h
  exact hb

/--
---
conclusion: Lax369799.ExpandedTransitions.evaluated_run_exists
---
Iterate parallel replacement at positive-rank vertices and leave nullary
labels unchanged. Encode the selected unary tuples as the run's edge types.
-/
theorem evaluated_run_exists {A : RankedSet} (L : Lax369799.Algebras.Language A)
    (hL : Lax369799.Algebras.UnfoldInvariantLanguage L) (hrec : Lax369799.Algebras.Recognizable L)
    [Fintype (Carrier (Accepting L) 1)] [Fintype (Carrier (Accepting L) 0)]
    (E : SyntacticAlgebra L)
    (D : WordCondition (Fintype.card (Carrier (Accepting L) 1))
      (Fintype.card (Carrier (Accepting L) 0)))
    (S : System A 0) (hS : S ∈ L) :
    ∃ r : Run (automaton L E D) S, AcceptingClass (Accepting L)
      (E.algebra.eval 0 (withLabels (ofSetSystem S.val) (runLabel L E D r.toLabelling))) := by
  classical
  let F := Accepting L
  let q := fun v : S.val.Vertex => quotientMap F _ (atomic (S.val.graph.label v).2)
  let G := fun n (a b : Carrier F n) => if n = 0 then b = a else
    ∃ bs : Fin n → Carrier F 1,
      (∀ i, Lax369799.ExtremalUnaryTypes.Selected L E (bs i)) ∧
      E.algebra.eval n (ofSetSystem (Lax369799.DeterministicElements.parallel bs)) = b ∧ ClassBelow F b a
  have hG : ∀ k (C : Lax369799.FiniteContexts.Context (Carrier F) k 0) (a : Carrier F k),
      AcceptingClass F (E.algebra.eval 0 (Lax369799.FiniteContexts.plug C (atomic a))) →
      ∃ b, G k a b ∧ AcceptingClass F (E.algebra.eval 0 (Lax369799.FiniteContexts.plug C (atomic b))) := by
    intro k C a ha
    by_cases hk : k = 0
    · exact ⟨a, by simp [G, hk], ha⟩
    · obtain ⟨bs, hs, hb, ha⟩ := SelectedParallel.accepting_parallel L hL hrec E (by omega) C a ha
      exact ⟨_, by simpa only [G, if_neg hk] using ⟨bs, hs, rfl, hb⟩, ha⟩
  have hq : AcceptingClass F (E.algebra.eval 0 (withLabels (ofSetSystem S.val) q)) := by
    change AcceptingClass F (E.algebra.eval 0
      (relabel (fun k a => quotientMap F k (atomic a)) (ofSetSystem S.val)))
    rw [ExpandedCertificates.input_evaluation L E]
    exact (ExpandedSyntacticAlgebra.recognition L hL S).mpr hS
  obtain ⟨z, hz, haz⟩ := FiniteLocalReplacement.simultaneous E.algebra {a | AcceptingClass F a} G hG
    (ofSetSystem S.val) q hq
  have pos (v : S.val.Vertex) (h : Rank S v ≠ 0) :
      ∃ bs : Fin (Rank S v) → Carrier F 1,
        (∀ i, Lax369799.ExtremalUnaryTypes.Selected L E (bs i)) ∧
        E.algebra.eval _ (ofSetSystem (Lax369799.DeterministicElements.parallel bs)) = z v ∧
          ClassBelow F (z v) (q v) := by
    have hv := hz v
    change (if Rank S v = 0 then z v = q v else _) at hv
    rw [if_neg h] at hv
    exact hv
  let bs := fun v : S.val.Vertex => if h : Rank S v = 0 then
    (fun i : Fin (Rank S v) => False.elim (by have := i.isLt; omega))
    else Classical.choose (pos v h)
  have hb (v : S.val.Vertex) (h : Rank S v ≠ 0) :
      (∀ i, Lax369799.ExtremalUnaryTypes.Selected L E (bs v i)) ∧
      E.algebra.eval _ (ofSetSystem (Lax369799.DeterministicElements.parallel (bs v))) = z v ∧
        ClassBelow F (z v) (q v) := by
    dsimp only [bs]
    rw [dif_neg h]
    exact Classical.choose_spec (pos v h)
  let r : Run (automaton L E D) S := {
    edgeType := fun v i => (Fintype.equivFin (Carrier F 1)) (bs v i)
    leafType := fun v h => (Fintype.equivFin (Carrier F 0))
      (quotientMap F 0 (atomic (h ▸ (S.val.graph.label v).2)))
    leaves := fun _ _ => rfl
    transitions := by
      intro v n h
      change (∀ i, Lax369799.ExtremalUnaryTypes.Selected L E
        (Lax369799.AlgebraicTransitions.decodeTypes
          (fun i => (Fintype.equivFin (Carrier F 1)) (bs v (Fin.cast h.symm i))) i)) ∧
        ClassBelow F (E.algebra.eval _ (ofSetSystem (Lax369799.DeterministicElements.parallel
        (Lax369799.AlgebraicTransitions.decodeTypes
          (fun i => (Fintype.equivFin (Carrier F 1)) (bs v (Fin.cast h.symm i)))))))
        (quotientMap F _ (atomic (h ▸ (S.val.graph.label v).2)))
      have hd : Lax369799.AlgebraicTransitions.decodeTypes
          (fun i => (Fintype.equivFin (Carrier F 1)) (bs v (Fin.cast h.symm i))) =
          (fun i => bs v (Fin.cast h.symm i)) := by
        funext i
        exact (Fintype.equivFin _).symm_apply_apply _
      rw [hd]
      have hv : Rank S v ≠ 0 := by omega
      refine ⟨fun i => (hb v hv).1 _, ?_⟩
      apply transition_cast_back L E h (S.val.graph.label v).2 (bs v)
      rw [(hb v hv).2.1]
      exact (hb v hv).2.2 }
  have he : runLabel L E D r.toLabelling = z := by
    funext v
    unfold runLabel
    dsimp only [Run.toLabelling]
    split_ifs with hv
    · have hl : r.leafType v hv = (Fintype.equivFin (Carrier F 0))
          (quotientMap F 0 (atomic (hv ▸ (S.val.graph.label v).2))) := rfl
      rw [hl, Equiv.symm_apply_apply]
      change (hv.symm ▸ quotientMap F 0 (atomic (hv ▸ (S.val.graph.label v).2)) : Carrier F (Rank S v)) = z v
      rw [input_cast L hv]
      have hzv := hz v
      change (if Rank S v = 0 then z v = q v else _) at hzv
      rw [if_pos hv] at hzv
      exact hzv.symm
    · change E.algebra.eval _ (ofSetSystem (Lax369799.DeterministicElements.parallel
        (fun i => (Fintype.equivFin (Carrier F 1)).symm ((Fintype.equivFin (Carrier F 1)) (bs v i))))) = z v
      simpa only [Equiv.symm_apply_apply] using (hb v hv).2.1
  exact ⟨r, by rw [he]; exact haz⟩

/--
---
conclusion: Lax369799.ExpandedTransitions.edge_preserves_choices
---
Every legal transition uses selected components. Their rank-one extremal
characterization gives choice preservation for each edge type.
-/
theorem edge_preserves_choices {A : RankedSet} (L : Lax369799.Algebras.Language A)
    [Fintype (Carrier (Accepting L) 1)] [Fintype (Carrier (Accepting L) 0)]
    (E : SyntacticAlgebra L)
    (D : WordCondition (Fintype.card (Carrier (Accepting L) 1))
      (Fintype.card (Carrier (Accepting L) 0)))
    {S : System A 0} (r : Run (automaton L E D) S) (v : S.val.Vertex) (i : Fin (Rank S v)) :
    Lax369799.ChoicePreservingUnary.PreservesChoices E.algebra
      ((Fintype.equivFin (Carrier (Accepting L) 1)).symm (r.edgeType v i)) := by
  have hn : Rank S v ≠ 0 := by have := i.isLt; omega
  obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero hn
  have hs := (r.transitions v n hn).1 (Fin.cast hn i)
  apply SelectedChoicePreservation.selected_preserves_choices L E
  exact hs

end Lax369799Proofs.ExpandedTransitions
