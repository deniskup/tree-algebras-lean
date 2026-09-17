import Lax369799Proofs.Flattening
import Lax369799Proofs.SumCovers
import Lax369799.SetAlgebraTheorems
import Lax369799.EvaluationTheorems
import Mathlib.Tactic.FinCases

namespace Lax369799Proofs.SumEvaluation
open Lax369799.RankedSystems Lax369799.Morphisms Lax369799.Flattening Lax369799.SetAlgebras
open Lax369799Proofs.Pullbacks Lax369799Proofs.MorphismTheorems

noncomputable def sumGraph {A : RankedSet} {n : ℕ} (S T : SetSystem A n) :
    Presentation A n (S.Vertex ⊕ T.Vertex) :=
  {
    label := Sum.elim S.graph.label T.graph.label
    initial := Sum.elim S.graph.initial T.graph.initial
    root := Sum.elim S.graph.root T.graph.root
    edge := fun v d t => match v with
      | .inl v => ∃ t', S.graph.edge v d t' ∧ t = Sum.map Sum.inl id t'
      | .inr v => ∃ t', T.graph.edge v d t' ∧ t = Sum.map Sum.inr id t'
    direction_valid := by
      intro v d t h
      cases v with
      | inl v => obtain ⟨t', ht, _⟩ := h; exact S.graph.direction_valid v d t' ht
      | inr v => obtain ⟨t', ht, _⟩ := h; exact T.graph.direction_valid v d t' ht }

theorem eval_cover {A : RankedSet} (E : SetAlgebra A) {n : ℕ}
    {S T : SetSystem A n} (f : Morphism S T) (hf : f.LocallySurjective) :
    E.eval n S = E.eval n T :=
  E.unfold_invariant n S T ⟨S, ⟨identity S, identity_surjective S⟩, ⟨f, hf⟩⟩

def binary {A : RankedSet} {n : ℕ} (S T : SetSystem A n) :
    SetSystem (SetSystem A) n where
  size := 2
  graph := {
    label := Fin.cases ⟨n, S⟩ (fun _ => ⟨n, T⟩)
    initial := Set.univ
    root := ∅
    edge := fun _ d t => ∃ i : Fin n, d = i.val ∧ t = .inr i
    direction_valid := by
      rintro v d t ⟨i, rfl, rfl⟩
      refine Fin.cases i.isLt (fun _ => i.isLt) v }
  reachable := fun v => ⟨v, Or.inl (Set.mem_univ v), .refl⟩

private def split {A : RankedSet} {n : ℕ} (S T : SetSystem A n) :
    ((v : (binary S T).Vertex) × (Inner (binary S T) v).Vertex) → S.Vertex ⊕ T.Vertex :=
  fun v => Fin.cases (fun w => .inl w) (fun _ w => .inr w) v.1 v.2

theorem binary_flatten_cover {A : RankedSet} {n : ℕ} (S T : SetSystem A n) :
    UnfoldsTo (sum S T) (flatten (binary S T)) := by
  classical
  let raw : Map (Lax369799Proofs.Flattening.graph (binary S T)) (sumGraph S T) := {
    toFun := split S T
    initial := by
      rintro ⟨v, w⟩ ⟨_, hw⟩
      fin_cases v <;> exact hw
    root := by
      rintro ⟨v, w⟩ (hw | ⟨hv, _⟩)
      · fin_cases v <;> exact hw
      · exact False.elim hv
    label := by rintro ⟨v, w⟩; fin_cases v <;> rfl
    edge := by
      rintro ⟨v, w⟩ d t ht
      fin_cases v
      all_goals
        rcases ht with ⟨u, hu, rfl⟩ | ⟨i, hi, ht⟩
        · exact ⟨.inl u, hu, rfl⟩
        · rcases ht with ⟨u, ⟨j, hj, he⟩, _⟩ | ⟨j, ⟨l, hl, he⟩, rfl⟩
          · cases he
          · have hj : j = l := Sum.inr.inj he
            have hi' : i = l := Fin.ext hl
            subst l
            subst j
            exact ⟨.inr i, hi, rfl⟩ }
  refine ⟨trimMap raw, trimMap_surjective raw ?_ ?_ ?_⟩
  · intro w hw
    cases w with
    | inl w => exact ⟨⟨(0 : Fin 2), w⟩, ⟨True.intro, hw⟩, rfl⟩
    | inr w => exact ⟨⟨(1 : Fin 2), w⟩, ⟨True.intro, hw⟩, rfl⟩
  · intro w hw
    cases w with
    | inl w => exact ⟨⟨(0 : Fin 2), w⟩, Or.inl hw, rfl⟩
    | inr w => exact ⟨⟨(1 : Fin 2), w⟩, Or.inl hw, rfl⟩
  · rintro ⟨v, w⟩ d t ht
    fin_cases v
    all_goals
      obtain ⟨s, hs, rfl⟩ := ht
      cases s with
      | inl u => first
        | exact ⟨.inl ⟨(0 : Fin 2), u⟩, Or.inl ⟨u, hs, rfl⟩, rfl⟩
        | exact ⟨.inl ⟨(1 : Fin 2), u⟩, Or.inl ⟨u, hs, rfl⟩, rfl⟩
      | inr i => exact ⟨.inr i, Or.inr ⟨i, hs, Or.inr ⟨i, ⟨i, rfl, rfl⟩, rfl⟩⟩, rfl⟩

theorem eval_binary_labels {A B : RankedSet} (E : SetAlgebra B)
    (f : RankedMap (SetSystem A) B) {n : ℕ} (S T : SetSystem A n) :
    E.eval n (relabel f (binary S T)) = meet E (f n S) (f n T) := by
  let raw : Map (sumGraph (atomic (f n S)) (atomic (f n T)))
      (relabel f (binary S T)).graph := {
    toFun := Sum.elim (fun _ => (0 : Fin 2)) (fun _ => (1 : Fin 2))
    initial := fun _ _ => True.intro
    root := by intro v hv; cases v <;> exact False.elim hv
    label := by intro v; cases v <;> rfl
    edge := by
      intro v d t ht
      cases v <;> obtain ⟨s, ⟨i, rfl, rfl⟩, rfl⟩ := ht <;> exact ⟨i, rfl, rfl⟩ }
  have hp : (project raw).LocallySurjective := by
    apply project_surjective raw
    · intro v hv
      fin_cases v
      · exact ⟨.inl (0 : Fin 1), True.intro, rfl⟩
      · exact ⟨.inr (0 : Fin 1), True.intro, rfl⟩
    · intro v hv; exact False.elim hv
    · intro v d t ht
      obtain ⟨i, rfl, rfl⟩ := ht
      cases v <;> exact ⟨.inr i, ⟨.inr i, ⟨i, rfl, rfl⟩, rfl⟩, rfl⟩
  exact (eval_cover E (project raw) hp).symm

/--
---
conclusion: Lax369799.EvaluationTheorems.eval_sum
---
Flatten a two-vertex pattern labelled by the two systems. Its flattening
covers their disjoint union; evaluating the labels gives the defining meet.
-/
theorem eval_sum {A : RankedSet} (E : SetAlgebra A) {n : ℕ} (S T : SetSystem A n) :
    E.eval n (sum S T) = meet E (E.eval n S) (E.eval n T) := by
  classical
  let P := relabel E.eval (binary S T)
  let raw : Map (sumGraph (atomic (E.eval n S)) (atomic (E.eval n T))) P.graph := {
    toFun := Sum.elim (fun _ => (0 : Fin 2)) (fun _ => (1 : Fin 2))
    initial := fun _ _ => True.intro
    root := by intro v hv; cases v <;> exact False.elim hv
    label := by intro v; cases v <;> rfl
    edge := by
      intro v d t ht
      cases v <;> obtain ⟨s, ⟨i, rfl, rfl⟩, rfl⟩ := ht <;> exact ⟨i, rfl, rfl⟩ }
  have hp : (project raw).LocallySurjective := by
    apply project_surjective raw
    · intro v hv
      fin_cases v
      · exact ⟨.inl (0 : Fin 1), True.intro, rfl⟩
      · exact ⟨.inr (0 : Fin 1), True.intro, rfl⟩
    · intro v hv; exact False.elim hv
    · intro v d t ht
      obtain ⟨i, rfl, rfl⟩ := ht
      cases v <;> exact ⟨.inr i, ⟨.inr i, ⟨i, rfl, rfl⟩, rfl⟩, rfl⟩
  obtain ⟨c, hc⟩ := binary_flatten_cover S T
  exact ((eval_cover E (project raw) hp).trans
    ((E.associative n (binary S T)).trans (eval_cover E c hc))).symm

private theorem eval_sum_assoc {A : RankedSet} (E : SetAlgebra A) {n : ℕ}
    (S T U : SetSystem A n) :
    E.eval n (sum (sum S T) U) = E.eval n (sum S (sum T U)) := by
  open SumCovers in
  have left := combineCover
    (enumerate (combine S.graph T.graph) (combine_reachable S.graph T.graph S.reachable T.reachable))
    (SumCovers.identity U.graph)
  open SumCovers in
  have right := combineCover (SumCovers.identity S.graph)
    (enumerate (combine T.graph U.graph) (combine_reachable T.graph U.graph T.reachable U.reachable))
  obtain ⟨l, hl⟩ := SumCovers.trim_cover left
  obtain ⟨r, hr⟩ := SumCovers.trim_cover right
  obtain ⟨m, hm⟩ := SumCovers.trim_cover (SumCovers.associate S.graph T.graph U.graph)
  simpa only [SumCovers.sum_eq_trim] using
    (eval_cover E l hl).symm.trans ((eval_cover E m hm).trans (eval_cover E r hr))

private theorem eval_sum_comm {A : RankedSet} (E : SetAlgebra A) {n : ℕ}
    (S T : SetSystem A n) : E.eval n (sum S T) = E.eval n (sum T S) := by
  obtain ⟨f, hf⟩ := SumCovers.trim_cover (SumCovers.swap S.graph T.graph)
  simpa only [SumCovers.sum_eq_trim] using eval_cover E f hf

/--
---
conclusion: Lax369799.SetAlgebraTheorems.meet_laws
---
Associativity of evaluation identifies evaluation of a disjoint union
with meet of its evaluations. The disjoint-union associator and swap are
covers. Idempotence also follows directly from the identity morphism axiom.
-/
theorem meet_laws {A : RankedSet} (E : SetAlgebra A) (n : ℕ) :
    (∀ a b c : A n, meet E (meet E a b) c = meet E a (meet E b c)) ∧
    (∀ a b : A n, meet E a b = meet E b a) ∧
    (∀ a : A n, meet E a a = a) := by
  refine ⟨?_, ?_, ?_⟩
  · intro a b c
    calc
      meet E (meet E a b) c = E.eval n (sum (sum (atomic a) (atomic b)) (atomic c)) := by
        rw [eval_sum, E.unit]; rfl
      _ = E.eval n (sum (atomic a) (sum (atomic b) (atomic c))) := eval_sum_assoc E _ _ _
      _ = meet E a (meet E b c) := by rw [eval_sum, E.unit]; rfl
  · intro a b
    exact eval_sum_comm E (atomic a) (atomic b)
  · intro a
    have h := E.morphism n (atomic a) (atomic a) ⟨Lax369799Proofs.MorphismTheorems.identity (atomic a)⟩
    change meet E (E.eval n (atomic a)) (E.eval n (atomic a)) = E.eval n (atomic a) at h
    simpa only [E.unit] using h

end Lax369799Proofs.SumEvaluation
