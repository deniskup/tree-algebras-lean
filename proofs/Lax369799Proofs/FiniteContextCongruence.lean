import Lax369799.FiniteContextCongruence
import Lax369799Proofs.FiniteContextualOrder

set_option backward.isDefEq.respectTransparency false
namespace Lax369799Proofs.FiniteContextCongruence
open Lax369799
open RankedSystems (RankedSet)
open FinitePresentations FiniteContexts FiniteContextCongruence

private theorem one {A B : RankedSet} (R R' : RelationFamily A)
    (hC : InContexts R R') (ht : ∀ n (S T U : FiniteSystem A n), R' n S T → R' n T U → R' n S U)
    (hi : ∀ n (S T : FiniteSystem A n), Isomorphic S T → R' n S T)
    {n : ℕ} (P : FiniteSystem B n)
    (q r : ∀ v : P.Vertex, FiniteSystem A (P.graph.label v).1) (v : P.Vertex)
    (he : ∀ w, w ≠ v → q w = r w) (hv : R _ (q v) (r v)) :
    R' n (flatten (withLabels P q)) (flatten (withLabels P r)) := by
  obtain ⟨C,hC'⟩ := FiniteContexts.extension (fun _ a => a) (FiniteContextualOrder.drill P q v)
  have hq := hC' (q v)
  have hr := hC' (r v)
  rw [FiniteContextualOrder.interpret_drill P q q v (fun _ _ => rfl)] at hq
  rw [FiniteContextualOrder.interpret_drill P q r v he] at hr
  have hq' : Isomorphic (flatten (withLabels P q)) (plug C (q v)) :=
    hq.elim (fun e => ⟨UntrimmedFlattening.isoSymm e⟩)
  exact ht n _ _ _ (hi n _ _ hq') (ht n _ _ _ (hC _ _ C (q v) (r v) hv) (hi n _ _ hr))

/--
---
conclusion: Lax369799.FiniteContextCongruence.context_iff_substitution
---
Replace the finitely many labels one at a time. Drilling the selected
vertex and extending the resulting context reduces each step to a
context test. The converse treats a context as a substitution, using
reflexivity for every ordinary letter outside its unique hole.
-/
theorem context_iff_substitution {A : RankedSet} (R R' : RelationFamily A)
    (hR : ∀ n (S : FiniteSystem A n), R n S S) (hR' : ∀ n (S : FiniteSystem A n), R' n S S)
    (htrans : ∀ n (S T U : FiniteSystem A n), R' n S T → R' n T U → R' n S U)
    (hiso : ∀ n (S T : FiniteSystem A n), Isomorphic S T → R' n S T) :
    InContexts R R' ↔ InSubstitutions R R' := by
  constructor
  · intro hC B n P q r hqr
    classical
    let mix (s : Finset P.Vertex) := fun v => if v ∈ s then r v else q v
    have hs (s : Finset P.Vertex) :
        R' n (flatten (withLabels P q)) (flatten (withLabels P (mix s))) := by
      induction s using Finset.induction_on with
      | empty => simpa only [mix,Finset.notMem_empty,if_false] using hR' n (flatten (withLabels P q))
      | @insert v s hv ih =>
        have step : R' n (flatten (withLabels P (mix s)))
            (flatten (withLabels P (mix (insert v s)))) := by
          apply one R R' hC htrans hiso P (mix s) (mix (insert v s)) v
          · intro w hw
            simp only [mix,Finset.mem_insert,hw,false_or]
          · simpa only [mix,if_neg hv,Finset.mem_insert_self,if_true] using hqr v
        exact htrans n _ _ _ ih step
    simpa only [mix,Finset.mem_univ,if_true] using hs Finset.univ
  · intro hF k n C S T hST
    have hl (v : C.system.Vertex) : R _
        (substitution S (C.system.graph.label v).1 (C.system.graph.label v).2)
        (substitution T (C.system.graph.label v).1 (C.system.graph.label v).2) := by
      generalize (C.system.graph.label v) = a
      obtain ⟨m,a⟩ := a
      cases a with
      | inl a => exact hR m _
      | inr e => obtain ⟨e⟩ := e; subst m; exact hST
    exact hF (Flattening.WithHole A k) n C.system
      (fun v => substitution S _ (C.system.graph.label v).2)
      (fun v => substitution T _ (C.system.graph.label v).2) hl

end Lax369799Proofs.FiniteContextCongruence
