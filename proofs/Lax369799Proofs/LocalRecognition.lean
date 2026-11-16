import Lax369799.LocalRecognition
import Lax369799Proofs.PathAlgebra

set_option backward.isDefEq.respectTransparency false
namespace Lax369799Proofs.LocalRecognition
open Lax369799.RankedSystems Lax369799.Algebras Lax369799.InitialAlgebra
open Lax369799.PathAlgebra

private theorem reachable {A : RankedSet} {n : ℕ} (S : System A n) (v : S.val.Vertex) :
    Relation.ReflTransGen S.val.graph.Step (initial S) v := by
  obtain ⟨r, hr, hp⟩ := S.val.reachable v
  rcases hr with hr | hr
  · have he : r = initial S := by
      have hi := Classical.choose_spec S.property.1
      rw [hi] at hr
      exact hr
    exact he ▸ hp
  · rw [S.property.2.1] at hr
    exact False.elim hr

def occurrenceLetter {A : RankedSet} (p : ∀ n, A n → Prop) : RankedMap A (Carrier Unit) :=
  fun n a _ out => match out with
    | .inl _ => p n a
    | .inr _ => True

theorem occurrence_iff {A : RankedSet} (p : ∀ n, A n → Prop) (S : System A 0) :
    Run (relabelSystem (occurrenceLetter p) S).val.graph (initial S) () (.inl ()) ↔
      ∃ v, p _ (S.val.graph.label v).2 := by
  constructor
  · intro h
    have hh {v q out} (h : Run (relabelSystem (occurrenceLetter p) S).val.graph v q out) :
        out = .inl () → ∃ w, p _ (S.val.graph.label w).2 := by
      induction h with
      | halt h => intro _; exact ⟨_, h⟩
      | exit d h he => intro h; cases h
      | step d h he ht ih => exact ih
    exact hh h rfl
  · rintro ⟨v, hv⟩
    have lift {u v} (hp : Relation.ReflTransGen S.val.graph.Step u v)
        (ht : Run (relabelSystem (occurrenceLetter p) S).val.graph v () (.inl ())) :
        Run (relabelSystem (occurrenceLetter p) S).val.graph u () (.inl ()) := by
      induction hp with
      | refl => exact ht
      | @tail b c hp he ih =>
        obtain ⟨d, hd⟩ := he
        exact ih (.step d ⟨⟨d, S.val.graph.direction_valid b d _ hd⟩, rfl, trivial⟩ hd ht)
    exact lift (reachable S v) (.halt hv)

/--
---
conclusion: Lax369799.LocalRecognition.occurrence
---
A one-state path summary may stop exactly at letters satisfying the
predicate and may otherwise traverse any direction.
-/
theorem occurrence {A : RankedSet} (p : ∀ n, A n → Prop) :
    Recognizable {S : System A 0 | ∃ v, p _ (S.val.graph.label v).2} := by
  obtain ⟨E, he⟩ := PathAlgebra.algebra Unit
  refine ⟨Carrier Unit, E, occurrenceLetter p, {a | .inl () ∈ a ()}, PathAlgebra.finite_carrier Unit, ?_⟩
  intro S
  rw [he]
  exact (occurrence_iff p S).symm

def edgeLetter {A : RankedSet} (p q : ∀ n, A n → Prop) : RankedMap A (Carrier Bool) :=
  fun n a b out => match out with
    | .inl _ => b = true ∧ q n a
    | .inr (_, r) => b = false ∧ (r = false ∨ (r = true ∧ p n a))

private theorem true_run {A : RankedSet} (p q : ∀ n, A n → Prop) (S : System A 0)
    {v out} (h : Run (relabelSystem (edgeLetter p q) S).val.graph v true out) :
    q _ (S.val.graph.label v).2 := by
  cases h with
  | halt h => exact h.2
  | exit d h he => obtain ⟨i, hi, hh⟩ := h; cases hh.1
  | step d h he ht => obtain ⟨i, hi, hh⟩ := h; cases hh.1

theorem edge_iff {A : RankedSet} (p q : ∀ n, A n → Prop) (S : System A 0) :
    Run (relabelSystem (edgeLetter p q) S).val.graph (initial S) false (.inl true) ↔
      ∃ v w d, p _ (S.val.graph.label v).2 ∧ q _ (S.val.graph.label w).2 ∧
        S.val.graph.edge v d (.inl w) := by
  constructor
  · intro h
    have hh {v b out} (h : Run (relabelSystem (edgeLetter p q) S).val.graph v b out) :
        b = false → out = .inl true → ∃ v w d, p _ (S.val.graph.label v).2 ∧
          q _ (S.val.graph.label w).2 ∧ S.val.graph.edge v d (.inl w) := by
      induction h with
      | halt h => intro hb _; exact False.elim (Bool.noConfusion (hb.symm.trans h.1))
      | exit d h he => intro _ ho; cases ho
      | @step v w b r out d h he ht ih =>
        intro hb ho
        obtain ⟨i, hi, hh⟩ := h
        rcases hh.2 with hr | ⟨hr, hp⟩
        · exact ih hr ho
        · subst r
          exact ⟨v, w, d, hp, true_run p q S ht, he⟩
    exact hh h rfl rfl
  · rintro ⟨v, w, d, hp, hq, he⟩
    have lift {u v} (hpath : Relation.ReflTransGen S.val.graph.Step u v)
        (ht : Run (relabelSystem (edgeLetter p q) S).val.graph v false (.inl true)) :
        Run (relabelSystem (edgeLetter p q) S).val.graph u false (.inl true) := by
      induction hpath with
      | refl => exact ht
      | @tail b c hpath hed ih =>
        obtain ⟨d, hd⟩ := hed
        exact ih (.step d ⟨⟨d, S.val.graph.direction_valid b d _ hd⟩, rfl, rfl, Or.inl rfl⟩ hd ht)
    apply lift (reachable S v)
    exact .step d ⟨⟨d, S.val.graph.direction_valid v d _ he⟩, rfl, rfl, Or.inr ⟨rfl, hp⟩⟩
      he (.halt ⟨rfl, hq⟩)

/--
---
conclusion: Lax369799.LocalRecognition.edge
---
One state searches along an arbitrary prefix. It then traverses one edge
from the first predicate and stops at the second predicate.
-/
theorem edge {A : RankedSet} (p q : ∀ n, A n → Prop) :
    Recognizable {S : System A 0 | ∃ v w d,
      p _ (S.val.graph.label v).2 ∧ q _ (S.val.graph.label w).2 ∧ S.val.graph.edge v d (.inl w)} := by
  obtain ⟨E, he⟩ := PathAlgebra.algebra Bool
  refine ⟨Carrier Bool, E, edgeLetter p q, {a | .inl true ∈ a false}, PathAlgebra.finite_carrier Bool, ?_⟩
  intro S
  rw [he]
  exact (edge_iff p q S).symm

end Lax369799Proofs.LocalRecognition
