import Lax369799.FiniteDecomposition
import Lax369799Proofs.FiniteCovers
import Lax369799Proofs.FiniteOuterMorphisms

namespace Lax369799Proofs.FiniteDecomposition
open Lax369799.RankedSystems (RankedSet)
open Lax369799.Flattening (WithHole IsHole)
open Lax369799.FinitePresentations Lax369799.FiniteContexts
open Lax369799.ContextDecomposition (Boundary CopyVertex recomposePresentation)
open Lax369799.PresentationCovers Lax369799.FiniteDecomposition

theorem hole_label {A : RankedSet} {k : ℕ} (C : Context A k 0) :
    C.system.graph.label (holeVertex C) = ⟨k, Sum.inr ⟨rfl⟩⟩ := by
  have H : IsHole (C.system.graph.label (holeVertex C)) := (Classical.choose_spec C.one_hole).1
  generalize C.system.graph.label (holeVertex C) = a at H ⊢
  rcases a with ⟨r, a⟩
  obtain ⟨⟨hr⟩, ha⟩ := H
  change k = r at hr
  subst r
  change a = Sum.inr ⟨rfl⟩ at ha
  exact congrArg (Sigma.mk k) ha

/--
---
conclusion: Lax369799.FiniteDecomposition.piece_has_no_hole
---
Every copied vertex differs from the unique hole vertex.
-/
theorem piece_has_no_hole {A : RankedSet} {k : ℕ} (C : Context A k 0)
    (i : Fin (k + 1)) (v : BodyVertex C) : ¬ IsHole ((piece C i).label v) := by
  intro hv
  exact v.property ((Classical.choose_spec C.one_hole).2 v.val hv)

private noncomputable def project {A : RankedSet} {k : ℕ} (C : Context A k 0) :
    CopyVertex k (BodyVertex C) → C.system.Vertex
  | none => holeVertex C
  | some (_, v) => v.val

private noncomputable def reconstructionCover {A : RankedSet} {k : ℕ}
    (C : Context A k 0) :
    Cover (recomposePresentation (boundary C) (piece C)) C.system.graph where
  toFun := project C
  label := by
    intro v
    cases v with
    | none => exact hole_label C
    | some v => rfl
  initial := by
    intro v hv
    cases v with
    | none => exact hv
    | some v =>
      rcases v with ⟨i, v⟩
      rcases hv with ⟨hi, hv⟩
      subst i
      rcases hv with ⟨_, hv⟩ | ⟨d, hd, _⟩
      · exact hv
      · exact False.elim (Fin.succ_ne_zero d hd.symm)
  root := by
    intro v hv
    cases v <;> exact hv
  edge := by
    intro v d t ht
    cases t with
    | inr j => exact Fin.elim0 j
    | inl w =>
      cases v with
      | none =>
        cases w with
        | none => obtain ⟨i, rfl, hi⟩ := ht; exact hi
        | some w =>
          rcases w with ⟨j, w⟩
          obtain ⟨i, rfl, rfl, hw⟩ := ht
          rcases hw with ⟨hi, _⟩ | ⟨j, hj, he⟩
          · exact False.elim (Fin.succ_ne_zero i hi)
          · have h : i = j := Fin.succ_inj.mp hj
            subst j
            exact he
      | some v =>
        cases w with
        | none => exact ht
        | some w => exact ht.2
  initial_lift := by
    intro w hw
    by_cases h : w = holeVertex C
    · subst w
      exact ⟨none, hw, rfl⟩
    · exact ⟨some (0, ⟨w, h⟩), ⟨rfl, Or.inl ⟨rfl, hw⟩⟩, rfl⟩
  root_lift := by
    intro w hw
    by_cases h : w = holeVertex C
    · subst w
      exact ⟨none, hw, rfl⟩
    · exact ⟨some (0, ⟨w, h⟩), hw, rfl⟩
  edge_lift := by
    intro v d t ht
    cases t with
    | inr j => exact Fin.elim0 j
    | inl w =>
      cases v with
      | none =>
        have hd : d < k := by
          have h := C.system.graph.direction_valid (holeVertex C) d (.inl w) ht
          simpa only [hole_label C] using h
        by_cases hw : w = holeVertex C
        · subst w
          exact ⟨.inl none, ⟨⟨d, hd⟩, rfl, ht⟩, rfl⟩
        · exact ⟨.inl (some ((⟨d, hd⟩ : Fin k).succ, ⟨w, hw⟩)),
            ⟨⟨d, hd⟩, rfl, rfl, Or.inr ⟨⟨d, hd⟩, rfl, ht⟩⟩, rfl⟩
      | some v =>
        by_cases hw : w = holeVertex C
        · subst w
          exact ⟨.inl none, ht, rfl⟩
        · exact ⟨.inl (some (v.1, ⟨w, hw⟩)), ⟨rfl, ht⟩, rfl⟩

/--
---
conclusion: Lax369799.FiniteDecomposition.decomposition_cover
---
Each non-hole vertex occurs in the entry piece, irrespective of its
reachability. The projection is therefore globally surjective as well as
locally surjective on marks and edges.
-/
theorem decomposition_cover {A : RankedSet} {k : ℕ} (C : Context A k 0) :
    ∃ f : Cover (recompose C).graph C.system.graph, Function.Surjective f.toFun := by
  classical
  let G := recomposePresentation (boundary C) (piece C)
  let e := Fintype.equivFin (CopyVertex k (BodyVertex C))
  let f := FiniteCovers.compose (FiniteCovers.isoCover (UntrimmedFlattening.isoSymm
    (UntrimmedFlattening.reindexIso G e))) (reconstructionCover C)
  refine ⟨f, ?_⟩
  intro v
  by_cases hv : v = holeVertex C
  · subst v
    exact ⟨e none, by simp [f, FiniteCovers.compose, FiniteCovers.isoCover,
      UntrimmedFlattening.isoSymm, UntrimmedFlattening.reindexIso, reconstructionCover, project]⟩
  · exact ⟨e (some (0, ⟨v, hv⟩)), by simp [f, FiniteCovers.compose, FiniteCovers.isoCover,
      UntrimmedFlattening.isoSymm, UntrimmedFlattening.reindexIso, reconstructionCover, project]⟩

/--
---
conclusion: Lax369799.FiniteDecomposition.recompose_one_hole
---
The new hole is the sole hole-labelled vertex, since all unary pieces
exclude the original hole. Enumeration preserves this uniqueness.
-/
theorem recompose_one_hole {A : RankedSet} {k : ℕ} (C : Context A k 0) :
    ∃! v, IsHole ((recompose C).graph.label v) := by
  classical
  let e := Fintype.equivFin (CopyVertex k (BodyVertex C))
  refine ⟨e none, ?_, ?_⟩
  · change IsHole ((recomposePresentation (boundary C) (piece C)).label (e.symm (e none)))
    rw [Equiv.symm_apply_apply]
    exact ⟨⟨rfl⟩, rfl⟩
  · intro v hv
    have he : e.symm v = none := by
      cases h : e.symm v with
      | none => rfl
      | some w =>
        change IsHole ((recomposePresentation (boundary C) (piece C)).label (e.symm v)) at hv
        rw [h] at hv
        exact False.elim (piece_has_no_hole C w.1 w.2 hv)
    exact e.symm.injective (he.trans (e.symm_apply_apply none).symm)

/--
---
conclusion: Lax369799.FiniteDecomposition.decomposition_evaluation
---
The recomposition is a context with a globally surjective cover of the
original. Evaluate substituted labels first and use invariance under
that cover. This retains roots introduced by labels at unreachable vertices.
-/
theorem decomposition_evaluation {A : RankedSet} (L : Lax369799.Algebras.Language A)
    (E : Lax369799.FiniteSyntacticAlgebra.Algebra (Lax369799.FiniteContextualOrder.Carrier (Lax369799.FiniteAcceptance.Accepting L)))
    (hE : ∀ n (S : FiniteSystem (FiniteSystem A) n),
      E.eval n (relabel (Lax369799.FiniteContextualOrder.quotientMap (Lax369799.FiniteAcceptance.Accepting L)) S) =
        Lax369799.FiniteContextualOrder.quotientMap (Lax369799.FiniteAcceptance.Accepting L) n (flatten S))
    {k : ℕ} (C : Context (Lax369799.FiniteContextualOrder.Carrier (Lax369799.FiniteAcceptance.Accepting L)) k 0) :
    ∃ D : Context (Lax369799.FiniteContextualOrder.Carrier (Lax369799.FiniteAcceptance.Accepting L)) k 0,
      D.system = recompose C ∧ ∀ a,
        E.eval 0 (plug D (atomic a)) = E.eval 0 (plug C (atomic a)) := by
  let D : Context (Lax369799.FiniteContextualOrder.Carrier (Lax369799.FiniteAcceptance.Accepting L)) k 0 :=
    ⟨recompose C, recompose_one_hole C⟩
  obtain ⟨f, hf⟩ := decomposition_cover C
  refine ⟨D, rfl, ?_⟩
  intro a
  rw [plug, plug, ← E.associative, ← E.associative]
  exact FiniteOuterMorphisms.evaluation_cover L E hE
    (FiniteOuterMorphisms.relabelCover (fun r b => E.eval r (substitution (atomic a) r b)) f) hf

end Lax369799Proofs.FiniteDecomposition
