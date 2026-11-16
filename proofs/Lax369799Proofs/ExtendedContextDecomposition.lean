import Lax369799.ExtendedContextDecomposition
import Lax369799Proofs.SetSystemAlgebras
import Lax369799Proofs.FiniteNormalForms

namespace Lax369799Proofs.ExtendedContextDecomposition
set_option backward.isDefEq.respectTransparency false
open Lax369799
open RankedSystems (RankedSet RankedMap Presentation)
open FinitePresentations FiniteContexts FiniteDecomposition
open Lax369799.FiniteNormalForms (ordinaryPiece ordinaryLetter)
open Lax369799.SetSystemAlgebras (SetAlgebra)
open PresentationCovers Lax369799Proofs.Pullbacks
open Lax369799Proofs.FiniteNormalForms (letterSubstitution)

private noncomputable def body {A : RankedSet} {k : ℕ} (C : Context A k 0) :=
  (Fintype.equivFin (BodyVertex C)).symm

private noncomputable def pieces {A : RankedSet} {k : ℕ} (C : Context A k 0)
    (i : Fin (k + 1)) : FiniteSystem A 1 := by
  classical
  exact enumerate (ordinaryPiece C i)

private def markers {A : RankedSet} {k : ℕ} (C : Context A k 0)
    (i : Fin (k + 1)) : Set ExtendedContexts.Marker := {m | match m with
  | .initial => Fin.cases (boundary C).initial (fun j => j ∈ (boundary C).loops) i
  | .root => i = 0 ∧ (boundary C).root}

private noncomputable def rawPieces {A : RankedSet} {k : ℕ} (C : Context A k 0) :
    ExtendedContexts.Pieces (FiniteSystem A) k := fun i => ⟨pieces C i, markers C i⟩

private noncomputable def evaluatedPieces {A : RankedSet} (E : SetAlgebra A) {k : ℕ}
    (C : Context A k 0) : ExtendedContexts.Pieces A k :=
  fun i => ⟨E.eval 1 (pieces C i), markers C i⟩

private noncomputable def pattern {A : RankedSet} {k : ℕ} (C : Context A k 0) (a : A k) :
    FiniteSystem (FiniteSystem A) 0 :=
  relabel (letterSubstitution (atomic a)) (ExtendedContexts.context (rawPieces C)).system

private noncomputable def position {A : RankedSet} {k : ℕ} (C : Context A k 0) (a : A k) :
    ((v : (pattern C a).Vertex) × (Inner (pattern C a).graph v).Vertex) → C.system.Vertex := by
  classical
  intro v
  exact Fin.cases (fun _ => holeVertex C)
    (fun i w => (body C w).val) v.1 v.2

private theorem body_label {A : RankedSet} {k : ℕ} (C : Context A k 0) (a : A k)
    (v : BodyVertex C) :
    (relabel (letterSubstitution a) C.system).graph.label v.val =
      ⟨(C.system.graph.label v.val).1, (ordinaryLetter C v).val⟩ := by
  change Sigma.mk _ (letterSubstitution a _ _) = _
  exact congrArg (fun b => Sigma.mk (C.system.graph.label v.val).1
    (letterSubstitution a _ b)) (ordinaryLetter C v).property

private theorem hole_label {A : RankedSet} {k : ℕ} (C : Context A k 0) (a : A k) :
    (relabel (letterSubstitution a) C.system).graph.label (holeVertex C) = ⟨k, a⟩ := by
  change Sigma.mk _ (letterSubstitution a _ _) = _
  rw [FiniteDecomposition.hole_label C]
  rfl

private theorem hole_exit {A : RankedSet} {k : ℕ} (C : Context A k 0) (a : A k)
    (d : ℕ) (w : (v : (pattern C a).Vertex) × (Inner (pattern C a).graph v).Vertex)
    (h : (pattern C a).graph.edge (0 : Fin (k + 2)) d (.inl w.1))
    (hw : w.2 ∈ (Inner (pattern C a).graph w.1).graph.initial) :
    C.system.graph.edge (holeVertex C) d (.inl (position C a w)) := by
  classical
  rcases w with ⟨v, w⟩
  cases v using Fin.cases with
  | zero =>
    rcases h with ⟨i, hd, he⟩ | ⟨i, hi, hd, he⟩
    · exact False.elim (Fin.succ_ne_zero i.succ (Sum.inl.inj he).symm)
    · subst d
      exact hi
  | succ j =>
    rcases h with ⟨i, hd, he⟩ | ⟨i, hi, hd, he⟩
    · have hji : j = i.succ := Fin.succ_inj.mp (Sum.inl.inj he)
      subst j
      subst d
      change ((i.succ = 0 ∧ _) ∨ ∃ l : Fin k, i.succ = l.succ ∧ _) at hw
      rcases hw with ⟨hi, _⟩ | ⟨l, hil, hl⟩
      · exact False.elim (Fin.succ_ne_zero i hi)
      · have hil : i = l := Fin.succ_inj.mp hil
        subst l
        exact hl
    · exact False.elim (Fin.succ_ne_zero j (Sum.inl.inj he))

private noncomputable def projectionMap {A : RankedSet} {k : ℕ}
    (C : Context A k 0) (a : A k) :
    Map (flattenPresentation (pattern C a).graph)
      (relabel (letterSubstitution a) C.system).graph := by
  classical
  exact {
    toFun := position C a
    label := by
      rintro ⟨v, w⟩
      cases v using Fin.cases with
      | zero => exact hole_label C a
      | succ i => exact body_label C a (body C w)
    initial := by
      rintro ⟨v, w⟩ ⟨hv, hw⟩
      cases v using Fin.cases with
      | zero =>
        rcases hv with hv | ⟨_, hv⟩
        · exact False.elim (Fin.succ_ne_zero (0 : Fin (k + 1)) hv.symm)
        · exact hv
      | succ i =>
        rcases hv with hv | ⟨hv, _⟩
        · have hi : i = 0 := Fin.succ_inj.mp hv
          subst i
          rcases hw with ⟨_, h⟩ | ⟨j, hj, _⟩
          · exact h
          · exact False.elim (Fin.succ_ne_zero j hj.symm)
        · exact False.elim (Fin.succ_ne_zero i hv)
    root := by
      rintro ⟨v, w⟩ h
      cases v using Fin.cases with
      | zero =>
        rcases h with h | ⟨h, _⟩
        · exact False.elim h
        · obtain ⟨_, i, hi⟩ := h
          exact hi.2
      | succ i =>
        rcases h with h | ⟨h, _⟩
        · exact h
        · exact False.elim (Fin.succ_ne_zero i h.1)
    edge := by
      rintro ⟨v, w⟩ d t h
      cases v using Fin.cases with
      | zero =>
        rcases h with ⟨u, ⟨i, _, hi⟩, _⟩ | ⟨i, ⟨j, hd, he⟩, ht⟩
        · cases hi
        · have hij : i = j := Sum.inr.inj he
          subst j
          subst d
          rcases ht with ⟨u, hu, hu', rfl⟩ | ⟨j, _, _⟩
          · exact hole_exit C a i.val u hu hu'
          · exact Fin.elim0 j
      | succ i =>
        rcases h with ⟨u, hu, rfl⟩ | ⟨j, hj, ht⟩
        · exact hu
        · rcases ht with ⟨⟨v', u⟩, hv', _, rfl⟩ | ⟨l, _, _⟩
          · have he : v' = (0 : Fin (k + 2)) := Sum.inl.inj hv'.2
            subst v'
            exact hj
          · exact Fin.elim0 l }


private noncomputable def projectionRawCover {A : RankedSet} {k : ℕ} (C : Context A k 0) (a : A k) :
    Cover (flattenPresentation (pattern C a).graph) (relabel (letterSubstitution a) C.system).graph := by
  classical
  let f := projectionMap C a
  refine {
    toFun := f.toFun
    label := f.label
    initial := f.initial
    root := f.root
    edge := f.edge
    initial_lift := ?_
    root_lift := ?_
    edge_lift := ?_ }
  · intro w hw
    by_cases he : w = holeVertex C
    · subst w
      exact ⟨⟨(0 : Fin (k + 2)), (0 : Fin 1)⟩,
        ⟨Or.inr ⟨rfl, hw⟩, True.intro⟩, rfl⟩
    · let b : BodyVertex C := ⟨w, he⟩
      refine ⟨⟨(0 : Fin (k + 1)).succ, (body C).symm b⟩, ⟨Or.inl rfl, ?_⟩, ?_⟩
      · change (ordinaryPiece C 0).initial (body C ((body C).symm b))
        rw [Equiv.apply_symm_apply]
        exact Or.inl ⟨rfl, hw⟩
      · change (body C ((body C).symm b)).val = w
        rw [Equiv.apply_symm_apply]
  · intro w hw
    by_cases he : w = holeVertex C
    · subst w
      exact ⟨⟨(0 : Fin (k + 2)), (0 : Fin 1)⟩,
        Or.inr ⟨⟨rfl, ⟨0, rfl, hw⟩⟩, True.intro⟩, rfl⟩
    · let b : BodyVertex C := ⟨w, he⟩
      refine ⟨⟨(0 : Fin (k + 1)).succ, (body C).symm b⟩, Or.inl ?_, ?_⟩
      · change (ordinaryPiece C 0).root (body C ((body C).symm b))
        rw [Equiv.apply_symm_apply]
        exact hw
      · change (body C ((body C).symm b)).val = w
        rw [Equiv.apply_symm_apply]
  · rintro ⟨v, u⟩ d t ht
    cases t with
    | inr i => exact Fin.elim0 i
    | inl w =>
      cases v using Fin.cases with
      | zero =>
        change C.system.graph.edge (holeVertex C) d (.inl w) at ht
        have hd : d < k := by
          have h := C.system.graph.direction_valid (holeVertex C) d (.inl w) ht
          simpa only [FiniteDecomposition.hole_label C] using h
        let i : Fin k := ⟨d, hd⟩
        by_cases he : w = holeVertex C
        · subst w
          exact ⟨.inl ⟨(0 : Fin (k + 2)), (0 : Fin 1)⟩,
            Or.inr ⟨i, ⟨i, rfl, rfl⟩,
              Or.inl ⟨⟨(0 : Fin (k + 2)), (0 : Fin 1)⟩,
                Or.inr ⟨i, ht, rfl, rfl⟩, True.intro, rfl⟩⟩, rfl⟩
        · let b : BodyVertex C := ⟨w, he⟩
          let q := (body C).symm b
          have hq : q ∈ (pieces C i.succ).graph.initial := by
            change (ordinaryPiece C i.succ).initial (body C q)
            rw [Equiv.apply_symm_apply]
            exact Or.inr ⟨i, rfl, ht⟩
          refine ⟨.inl ⟨i.succ.succ, q⟩,
            Or.inr ⟨i, ⟨i, rfl, rfl⟩,
              Or.inl ⟨⟨i.succ.succ, q⟩, Or.inl ⟨i, rfl, rfl⟩, hq, rfl⟩⟩, ?_⟩
          change Sum.inl (body C q).val = .inl w
          rw [Equiv.apply_symm_apply]
      | succ j =>
        change C.system.graph.edge (body C u).val d (.inl w) at ht
        by_cases he : w = holeVertex C
        · subst w
          exact ⟨.inl ⟨(0 : Fin (k + 2)), (0 : Fin 1)⟩,
            Or.inr ⟨(0 : Fin 1), ht,
              Or.inl ⟨⟨(0 : Fin (k + 2)), (0 : Fin 1)⟩, ⟨rfl, rfl⟩, True.intro, rfl⟩⟩, rfl⟩
        · let b : BodyVertex C := ⟨w, he⟩
          let q := (body C).symm b
          have hq : (pieces C j).graph.edge u d (.inl q) := by
            change (ordinaryPiece C j).edge (body C u) d
              (.inl (body C q))
            rw [Equiv.apply_symm_apply]
            exact ht
          refine ⟨.inl ⟨j.succ, q⟩, Or.inl ⟨q, hq, rfl⟩, ?_⟩
          change Sum.inl (body C q).val = .inl w
          rw [Equiv.apply_symm_apply]

private theorem projection_surjective {A : RankedSet} {k : ℕ} (C : Context A k 0) (a : A k) :
    Function.Surjective (projectionRawCover C a).toFun := by
  classical
  intro w
  by_cases hw : w = holeVertex C
  · subst w
    exact ⟨⟨(0 : Fin (k + 2)), (0 : Fin 1)⟩, rfl⟩
  · refine ⟨⟨(0 : Fin (k + 1)).succ, (body C).symm ⟨w, hw⟩⟩, ?_⟩
    change (body C ((body C).symm ⟨w, hw⟩)).val = w
    rw [Equiv.apply_symm_apply]

private theorem projection_cover {A : RankedSet} {k : ℕ} (C : Context A k 0) (a : A k) :
    ∃ f : Cover (flatten (pattern C a)).graph (relabel (letterSubstitution a) C.system).graph,
      Function.Surjective f.toFun := by
  classical
  let G := flattenPresentation (pattern C a).graph
  let e := Fintype.equivFin ((v : (pattern C a).Vertex) × (Inner (pattern C a).graph v).Vertex)
  let f := FiniteCovers.compose (FiniteCovers.isoCover (UntrimmedFlattening.isoSymm
    (UntrimmedFlattening.reindexIso G e))) (projectionRawCover C a)
  refine ⟨f, ?_⟩
  intro w
  obtain ⟨v, hv⟩ := projection_surjective C a w
  refine ⟨e v, ?_⟩
  change (projectionRawCover C a).toFun (e.symm (e v)) = w
  rw [Equiv.symm_apply_apply]
  exact hv

private theorem evaluated_pattern {A : RankedSet} (E : SetAlgebra A) {k : ℕ}
    (C : Context A k 0) (a : A k) :
    relabel E.eval (pattern C a) = relabel (letterSubstitution a)
      (ExtendedContexts.context (evaluatedPieces E C)).system := by
  classical
  dsimp only [pattern, rawPieces, evaluatedPieces, relabel, ExtendedContexts.context,
    ExtremalContexts.normalPresentation]
  congr 1
  congr 1
  funext v
  cases v using Fin.cases with
  | zero =>
    change Sigma.mk k (E.eval k (atomic a)) = Sigma.mk k a
    rw [E.unit]
  | succ i => rfl

/--
---
conclusion: Lax369799.ExtendedContextDecomposition.context_decomposition
---
Expand the unpruned unary pieces and project each copied body vertex to
its original. The projection is a folding on all vertices and restores
initial marks, roots, and self-loops separately. Associativity then
replaces the pieces by their evaluations.
-/
theorem context_decomposition {A : RankedSet} (E : SetAlgebra A)
    {k : ℕ} (C : Context A k 0) :
    ∃ p : ExtendedContexts.Pieces A k, ∀ a : A k,
      E.eval 0 (plug (ExtendedContexts.context p) (atomic a)) = E.eval 0 (plug C (atomic a)) := by
  refine ⟨evaluatedPieces E C, ?_⟩
  intro a
  let N := ExtendedContexts.context (evaluatedPieces E C)
  obtain ⟨g, hg⟩ := projection_cover C a
  calc
    E.eval 0 (plug N (atomic a)) = E.eval 0 (relabel (letterSubstitution a) N.system) :=
      E.isomorphic 0 _ _ (FiniteNormalForms.plug_atomic_iso N a)
    _ = E.eval 0 (relabel E.eval (pattern C a)) := congrArg (E.eval 0) (evaluated_pattern E C a).symm
    _ = E.eval 0 (flatten (pattern C a)) := E.associative 0 (pattern C a)
    _ = E.eval 0 (relabel (letterSubstitution a) C.system) :=
      SetSystemAlgebras.folding_invariance E _ _ g hg
    _ = E.eval 0 (plug C (atomic a)) :=
      (E.isomorphic 0 _ _ (FiniteNormalForms.plug_atomic_iso C a)).symm

end Lax369799Proofs.ExtendedContextDecomposition
