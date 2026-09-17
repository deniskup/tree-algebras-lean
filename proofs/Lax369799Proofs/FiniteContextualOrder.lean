import Lax369799.FiniteContextualOrder
import Lax369799Proofs.FiniteContexts

namespace Lax369799Proofs.FiniteContextualOrder
open Lax369799.RankedSystems (RankedSet RankedMap Symbol)
open Lax369799.FinitePresentations Lax369799.FiniteContexts Lax369799.FiniteContextualOrder

/--
---
conclusion: Lax369799.FiniteContextualOrder.contextual_congruence
---
Compose the two testing contexts using unpruned substitution. The
associativity isomorphisms transfer the acceptance tests in both cases.
-/
theorem contextual_congruence {A : RankedSet} (F : ClosedProperty A) (hF : IsoInvariant F)
    {k n : ℕ} (C : Context A k n) (S T : FiniteSystem A k) (h : Below F S T) :
    Below F (plug C S) (plug C T) := by
  intro D hD
  obtain ⟨E, _, he⟩ := FiniteContexts.composition D C
  exact (hF _ _ (he T)).mp (h E ((hF _ _ (he S)).mpr hD))

private def identityContext (A : RankedSet) (n : ℕ) : Context A n n where
  system := atomic (A := Lax369799.Flattening.WithHole A n) (Sum.inr ⟨rfl⟩)
  one_hole := ⟨(0 : Fin 1), ⟨⟨rfl⟩, rfl⟩, fun _ _ => Subsingleton.elim (α := Fin 1) _ _⟩

/--
---
conclusion: Lax369799.FiniteContextualOrder.contextual_acceptance
---
The atomic hole is the identity context, by the outer atomic unit law.
-/
theorem contextual_acceptance {A : RankedSet} (F : ClosedProperty A) (hF : IsoInvariant F)
    (S T : FiniteSystem A 0) (h : Below F S T) : S ∈ F → T ∈ F := by
  intro hS
  have unit (U : FiniteSystem A 0) : Isomorphic (plug (identityContext A 0) U) U :=
    UntrimmedFlattening.outer_atomic U
  exact (hF _ _ (unit T)).mp (h (identityContext A 0) ((hF _ _ (unit S)).mpr hS))

/--
---
conclusion: Lax369799.FiniteContextualOrder.contextual_iso
---
Lift the argument isomorphism through each context. Isomorphism invariance
then identifies its two acceptance tests.
-/
theorem contextual_iso {A : RankedSet} (F : ClosedProperty A) (hF : IsoInvariant F)
    {n : ℕ} (S T : FiniteSystem A n) (h : Isomorphic S T) : Equivalent F S T := by
  have hc (C : Context A n 0) : Isomorphic (plug C S) (plug C T) := by
    apply UntrimmedFlattening.flatten_labels_iso C.system (substitution S) (substitution T)
    intro r a
    cases a with
    | inl a => exact ⟨UntrimmedFlattening.isoRefl _⟩
    | inr eq => obtain ⟨he⟩ := eq; subst r; exact h
  exact ⟨fun C => (hF _ _ (hc C)).mp, fun C => (hF _ _ (hc C)).mpr⟩

private noncomputable def drill {A B : RankedSet} {n : ℕ} (P : FiniteSystem B n)
    (q : ∀ v : P.Vertex, FiniteSystem A (P.graph.label v).1) (v : P.Vertex) :
    Context (FiniteSystem A) (P.graph.label v).1 n := by
  classical
  refine ⟨⟨P.size, {
    label := fun w => if w = v then ⟨(P.graph.label v).1, Sum.inr ⟨rfl⟩⟩
      else ⟨(P.graph.label w).1, Sum.inl (q w)⟩
    initial := P.graph.initial
    root := P.graph.root
    edge := P.graph.edge
    direction_valid := ?_ }⟩, ?_⟩
  · intro w d t h
    by_cases hw : w = v
    · subst w
      simpa using P.graph.direction_valid v d t h
    · simpa only [if_neg hw] using P.graph.direction_valid w d t h
  · refine ⟨v, ?_, ?_⟩
    · change Lax369799.Flattening.IsHole (if v = v then _ else _)
      rw [if_pos rfl]
      exact ⟨⟨rfl⟩, rfl⟩
    · intro w h
      by_cases hw : w = v
      · exact hw
      · simp only [if_neg hw] at h
        obtain ⟨eq, he⟩ := h
        cases he

private theorem interpret_drill {A B : RankedSet} {n : ℕ} (P : FiniteSystem B n)
    (q r : ∀ v : P.Vertex, FiniteSystem A (P.graph.label v).1) (v : P.Vertex)
    (h : ∀ w, w ≠ v → q w = r w) :
    relabel (interpretation (fun _ a => a) (r v)) (drill P q v).system = withLabels P r := by
  classical
  dsimp only [drill, relabel, withLabels]
  congr 1
  congr 1
  funext w
  let interpretSymbol (a : Symbol (Lax369799.Flattening.WithHole (FiniteSystem A) (P.graph.label v).1)) :
      Symbol (FiniteSystem A) := ⟨a.1, interpretation (fun _ a => a) (r v) a.1 a.2⟩
  by_cases hw : w = v
  · subst w
    exact congrArg interpretSymbol (if_pos (rfl : v = v))
  · exact (congrArg interpretSymbol (if_neg hw)).trans
      (congrArg (Sigma.mk (P.graph.label w).1) (h w hw))

private theorem change_one {A B : RankedSet} (F : ClosedProperty A) (hF : IsoInvariant F)
    {n : ℕ} (P : FiniteSystem B n)
    (q r : ∀ v : P.Vertex, FiniteSystem A (P.graph.label v).1) (v : P.Vertex)
    (he : ∀ w, w ≠ v → q w = r w) (hv : Below F (q v) (r v)) :
    Below F (flatten (withLabels P q)) (flatten (withLabels P r)) := by
  obtain ⟨C, hc⟩ := FiniteContexts.extension (fun _ a => a) (drill P q v)
  have hq := hc (q v)
  have hr := hc (r v)
  rw [interpret_drill P q q v (fun _ _ => rfl)] at hq
  rw [interpret_drill P q r v he] at hr
  have h1 := (contextual_iso F hF _ _ hq).2
  have h2 := contextual_congruence F hF C (q v) (r v) hv
  have h3 := (contextual_iso F hF _ _ hr).1
  exact fun D hD => h3 D (h2 D (h1 D hD))

/--
---
conclusion: Lax369799.FiniteContextualOrder.flatten_monotone
---
Replace the finitely many labels one at a time. Drilling a hole at the
selected vertex and extending that context by the other presentations
reduces each replacement to contextual monotonicity.
-/
theorem flatten_monotone {A B : RankedSet} (F : ClosedProperty A) (hF : IsoInvariant F)
    {n : ℕ} (P : FiniteSystem B n)
    (q r : ∀ v : P.Vertex, FiniteSystem A (P.graph.label v).1)
    (h : ∀ v, Below F (q v) (r v)) :
    Below F (flatten (withLabels P q)) (flatten (withLabels P r)) := by
  classical
  let mix (s : Finset P.Vertex) := fun v => if v ∈ s then r v else q v
  have hs (s : Finset P.Vertex) :
      Below F (flatten (withLabels P q)) (flatten (withLabels P (mix s))) := by
    induction s using Finset.induction_on with
    | empty => simpa only [mix, Finset.notMem_empty, if_false] using
        (show Below F (flatten (withLabels P q)) (flatten (withLabels P q)) from fun _ => id)
    | @insert v s hv ih =>
      have step : Below F (flatten (withLabels P (mix s)))
          (flatten (withLabels P (mix (insert v s)))) := by
        apply change_one F hF P (mix s) (mix (insert v s)) v
        · intro w hw
          simp only [mix, Finset.mem_insert, hw, false_or]
        · simpa only [mix, if_neg hv, Finset.mem_insert_self, if_true] using h v
      exact fun D hD => step D (ih D hD)
  simpa only [mix, Finset.mem_univ, if_true] using hs Finset.univ

end Lax369799Proofs.FiniteContextualOrder
