import Lax369799.FiniteNormalForms
import Lax369799Proofs.FinitePlant
import Lax369799Proofs.FiniteDecomposition

namespace Lax369799Proofs.FiniteNormalForms
open Lax369799.RankedSystems (RankedSet RankedMap Presentation)
open Lax369799.Flattening (WithHole IsHole)
open Lax369799.FinitePresentations Lax369799.FiniteContexts
open Lax369799.FiniteDecomposition Lax369799.FiniteNormalForms Lax369799.FiniteSyntacticAlgebra
open Lax369799.PresentationCovers Lax369799Proofs.Pullbacks

def letterSubstitution {A : RankedSet} {k : ℕ} (a : A k) : RankedMap (WithHole A k) A :=
  fun _ b => match b with
    | .inl b => b
    | .inr ⟨h⟩ => h ▸ a

theorem plug_atomic_iso {A : RankedSet} {k n : ℕ} (C : Context A k n) (a : A k) :
    Isomorphic (plug C (atomic a)) (relabel (letterSubstitution a) C.system) := by
  have he : relabel (substitution (atomic a)) C.system =
      relabel (fun _ b => atomic b) (relabel (letterSubstitution a) C.system) := by
    change relabel (substitution (atomic a)) C.system =
      relabel (fun r b => atomic (letterSubstitution a r b)) C.system
    apply congrArg (fun f : RankedMap (WithHole _ k) (FiniteSystem _) => relabel f C.system)
    funext r b
    cases b with
    | inl b => rfl
    | inr h => obtain ⟨h⟩ := h; subst r; rfl
  unfold plug
  rw [he]
  exact UntrimmedFlattening.inner_atomic _

private theorem eval_plant_atomic {A : RankedSet} (E : Algebra A) {k n : ℕ}
    (C : Context A k n) (a : A k) :
    E.eval n (plant (plug C (atomic a))) = E.eval n (plant (relabel (letterSubstitution a) C.system)) := by
  obtain ⟨f⟩ := plug_atomic_iso C a
  exact E.isomorphic n _ _ ⟨FinitePlant.plantIso f⟩

private noncomputable def body {A : RankedSet} {k : ℕ} (C : Context A k 0) :=
  (Fintype.equivFin (BodyVertex C)).symm

private noncomputable def pieces {A : RankedSet} {k : ℕ} (C : Context A k 0)
    (i : Fin (k + 1)) : FiniteSystem A 1 := by
  classical
  exact enumerate (ordinaryPiece C i)

private noncomputable def pattern {A : RankedSet} {k : ℕ} (C : Context A k 0) (a : A k) :
    FiniteSystem (FiniteSystem A) 0 :=
  relabel (letterSubstitution (atomic a))
    (normalContext (plantedBoundary C) (pieces C)).system

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
      (plant (relabel (letterSubstitution a) C.system)).graph := by
  classical
  exact {
    toFun := position C a
    label := by
      rintro ⟨v, w⟩
      cases v using Fin.cases with
      | zero => exact hole_label C a
      | succ i => exact body_label C a (body C w)
    initial := fun _ h => False.elim h.1
    root := by
      rintro ⟨v, w⟩ h
      cases v using Fin.cases with
      | zero =>
        rcases h with h | ⟨h, _⟩
        · exact False.elim h
        · rcases h with h | ⟨_, h⟩
          · exact False.elim (Fin.succ_ne_zero (0 : Fin (k + 1)) h.symm)
          · exact h.elim Or.inr Or.inl
      | succ i =>
        rcases h with h | ⟨h, hw⟩
        · exact Or.inl h
        · rcases h with h | ⟨h, _⟩
          · have hi : i = 0 := Fin.succ_inj.mp h
            subst i
            change ((0 = 0 ∧ _) ∨ ∃ j : Fin k, 0 = j.succ ∧ _) at hw
            rcases hw with ⟨_, hw⟩ | ⟨j, hj, _⟩
            · exact Or.inr hw
            · exact False.elim (Fin.succ_ne_zero j hj.symm)
          · exact False.elim (Fin.succ_ne_zero i h)
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
    Cover (flattenPresentation (pattern C a).graph) (plant (relabel (letterSubstitution a) C.system)).graph := by
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
  · intro w hw; exact False.elim hw
  · intro w hw
    by_cases he : w = holeVertex C
    · subst w
      exact ⟨⟨(0 : Fin (k + 2)), (0 : Fin 1)⟩,
        Or.inr ⟨Or.inr ⟨rfl, hw.elim Or.inr Or.inl⟩, True.intro⟩, rfl⟩
    · let b : BodyVertex C := ⟨w, he⟩
      refine ⟨⟨(0 : Fin (k + 1)).succ, (body C).symm b⟩, ?_, ?_⟩
      · rcases hw with hw | hw
        · apply Or.inl
          change (ordinaryPiece C 0).root (body C ((body C).symm b))
          rw [Equiv.apply_symm_apply]
          exact hw
        · refine Or.inr ⟨Or.inl rfl, ?_⟩
          change (ordinaryPiece C 0).initial (body C ((body C).symm b))
          rw [Equiv.apply_symm_apply]
          exact Or.inl ⟨rfl, hw⟩
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
    ∃ f : Cover (flatten (pattern C a)).graph (plant (relabel (letterSubstitution a) C.system)).graph,
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

private theorem evaluated_pattern {A : RankedSet} (E : Algebra A) {k : ℕ}
    (C : Context A k 0) (a : A k) :
    relabel E.eval (pattern C a) = relabel (letterSubstitution a)
      (normalContext (plantedBoundary C) (pieceValue E C)).system := by
  classical
  dsimp only [pattern, relabel, normalContext, ofSetSystem, Lax369799.ExtremalContexts.normalContext,
    Lax369799.ExtremalContexts.normalSystem, Lax369799.ExtremalContexts.normalPresentation]
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
conclusion: Lax369799.FiniteNormalForms.algebraic_decomposition
---
Flatten the normal pattern labelled by the unpruned unary pieces. Its
projection onto the planted original context covers all vertices and
lifts marks and edges. Cover invariance and associativity replace each
piece by its unary value.
-/
theorem algebraic_decomposition {A : RankedSet} (E : Algebra A)
    (hcover : ∀ n (S T : FiniteSystem A n) (f : Cover S.graph T.graph),
      Function.Surjective f.toFun → E.eval n S = E.eval n T)
    {k : ℕ} (C : Context A k 0) (a : A k) :
    E.eval 0 (plug (normalContext (plantedBoundary C) (pieceValue E C)) (atomic a)) =
      E.eval 0 (plant (plug C (atomic a))) := by
  let N := normalContext (plantedBoundary C) (pieceValue E C)
  obtain ⟨g, hg⟩ := projection_cover C a
  calc
    E.eval 0 (plug N (atomic a)) = E.eval 0 (relabel (letterSubstitution a) N.system) :=
      E.isomorphic 0 _ _ (plug_atomic_iso N a)
    _ = E.eval 0 (relabel E.eval (pattern C a)) := congrArg (E.eval 0) (evaluated_pattern E C a).symm
    _ = E.eval 0 (flatten (pattern C a)) := E.associative 0 (pattern C a)
    _ = E.eval 0 (plant (relabel (letterSubstitution a) C.system)) := hcover 0 _ _ g hg
    _ = E.eval 0 (plant (plug C (atomic a))) := (eval_plant_atomic E C a).symm

end Lax369799Proofs.FiniteNormalForms
