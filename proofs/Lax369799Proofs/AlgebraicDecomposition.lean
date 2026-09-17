import Lax369799.AlgebraicDecomposition
import Lax369799Proofs.AtomicFlattening
import Lax369799Proofs.ContextDecomposition
import Lax369799Proofs.SetAlgebraTheorems

namespace Lax369799Proofs.AlgebraicDecomposition
open Lax369799.RankedSystems Lax369799.Morphisms Lax369799.Flattening
open Lax369799.ContextDecomposition Lax369799.AlgebraicDecomposition Lax369799.SetAlgebras
open Lax369799.PresentationCovers Lax369799Proofs.Pullbacks

def letterSubstitution {A : RankedSet} {k : ℕ} (a : A k) : RankedMap (WithHole A k) A :=
  fun _ b => match b with
    | .inl b => b
    | .inr ⟨h⟩ => h ▸ a

theorem plug_atomic_cover {A : RankedSet} {k n : ℕ} (C : SetContext A k n) (a : A k) :
    UnfoldsTo (relabel (letterSubstitution a) C.system) (plug C (atomic a)) := by
  have he : relabel (substitution (atomic a)) C.system =
      relabel (fun _ b => atomic b) (relabel (letterSubstitution a) C.system) := by
    change relabel (substitution (atomic a)) C.system =
      relabel (fun r b => atomic (letterSubstitution a r b)) C.system
    apply congrArg (fun f : RankedMap (WithHole _ k) (SetSystem _) => relabel f C.system)
    funext r b
    cases b with
    | inl b => rfl
    | inr h => obtain ⟨h⟩ := h; subst r; rfl
  unfold plug
  rw [he]
  exact AtomicFlattening.atomic_flatten_cover _

private theorem eval_plant_atomic {A : RankedSet} (E : SetAlgebra A) {k n : ℕ}
    (C : SetContext A k n) (a : A k) :
    E.eval n (plant (plug C (atomic a))) = E.eval n (plant (relabel (letterSubstitution a) C.system)) := by
  obtain ⟨f, hf⟩ := plug_atomic_cover C a
  exact SumEvaluation.eval_cover E (SetAlgebraTheorems.plantMap f)
    (SetAlgebraTheorems.plant_surjective f hf)

private noncomputable def pieces {A : RankedSet} {k : ℕ} (C : SetContext A k 0)
    (i : Fin (k + 1)) : SetSystem A 1 := by
  classical
  exact trim (ordinaryPiece C i)

private noncomputable def pattern {A : RankedSet} {k : ℕ} (C : SetContext A k 0) (a : A k) :
    SetSystem (SetSystem A) 0 :=
  relabel (letterSubstitution (atomic a))
    (Lax369799.ExtremalContexts.normalContext (plantedBoundary C) (pieces C)).system

private noncomputable def position {A : RankedSet} {k : ℕ} (C : SetContext A k 0) (a : A k) :
    ((v : (pattern C a).Vertex) × (Inner (pattern C a) v).Vertex) → C.system.Vertex := by
  classical
  intro v
  exact Fin.cases (fun _ => holeVertex C)
    (fun i w => (vertex (ordinaryPiece C i) w).val) v.1 v.2

private theorem body_label {A : RankedSet} {k : ℕ} (C : SetContext A k 0) (a : A k)
    (v : BodyVertex C) :
    (relabel (letterSubstitution a) C.system).graph.label v.val =
      ⟨(C.system.graph.label v.val).1, (ordinaryLetter C v).val⟩ := by
  change Sigma.mk _ (letterSubstitution a _ _) = _
  exact congrArg (fun b => Sigma.mk (C.system.graph.label v.val).1
    (letterSubstitution a _ b)) (ordinaryLetter C v).property

private theorem hole_label {A : RankedSet} {k : ℕ} (C : SetContext A k 0) (a : A k) :
    (relabel (letterSubstitution a) C.system).graph.label (holeVertex C) = ⟨k, a⟩ := by
  change Sigma.mk _ (letterSubstitution a _ _) = _
  rw [ContextDecomposition.hole_label C]
  rfl

private theorem hole_exit {A : RankedSet} {k : ℕ} (C : SetContext A k 0) (a : A k)
    (d : ℕ) (w : (v : (pattern C a).Vertex) × (Inner (pattern C a) v).Vertex)
    (h : (pattern C a).graph.edge (0 : Fin (k + 2)) d (.inl w.1))
    (hw : w.2 ∈ (Inner (pattern C a) w.1).graph.initial) :
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
    (C : SetContext A k 0) (a : A k) :
    Map (Lax369799Proofs.Flattening.graph (pattern C a))
      (plant (relabel (letterSubstitution a) C.system)).graph := by
  classical
  exact {
    toFun := position C a
    label := by
      rintro ⟨v, w⟩
      cases v using Fin.cases with
      | zero => exact hole_label C a
      | succ i => exact body_label C a (vertex (ordinaryPiece C i) w)
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

private theorem projection_cover {A : RankedSet} {k : ℕ} (C : SetContext A k 0) (a : A k) :
    UnfoldsTo (plant (relabel (letterSubstitution a) C.system)) (flatten (pattern C a)) := by
  classical
  refine ⟨project (projectionMap C a), project_surjective (projectionMap C a) ?_ ?_ ?_⟩
  · intro w hw; exact False.elim hw
  · intro w hw
    by_cases he : w = holeVertex C
    · subst w
      exact ⟨⟨(0 : Fin (k + 2)), (0 : Fin 1)⟩,
        Or.inr ⟨Or.inr ⟨rfl, hw.elim Or.inr Or.inl⟩, True.intro⟩, rfl⟩
    · let b : BodyVertex C := ⟨w, he⟩
      have hb : (ordinaryPiece C 0).Reachable b :=
        ⟨b, hw.elim Or.inr (fun h => Or.inl (Or.inl ⟨rfl, h⟩)), .refl⟩
      refine ⟨⟨(0 : Fin (k + 1)).succ, index (ordinaryPiece C 0) ⟨b, hb⟩⟩, ?_, ?_⟩
      · rcases hw with hw | hw
        · apply Or.inl
          change (ordinaryPiece C 0).root (vertex (ordinaryPiece C 0) (index (ordinaryPiece C 0) _))
          rw [vertex_index]
          exact hw
        · refine Or.inr ⟨Or.inl rfl, ?_⟩
          change (ordinaryPiece C 0).initial (vertex (ordinaryPiece C 0) (index (ordinaryPiece C 0) _))
          rw [vertex_index]
          exact Or.inl ⟨rfl, hw⟩
      · change (vertex (ordinaryPiece C 0) (index (ordinaryPiece C 0) _)).val = w
        rw [vertex_index]
  · rintro ⟨v, u⟩ d t ht
    cases t with
    | inr i => exact Fin.elim0 i
    | inl w =>
      cases v using Fin.cases with
      | zero =>
        change C.system.graph.edge (holeVertex C) d (.inl w) at ht
        have hd : d < k := by
          have h := C.system.graph.direction_valid (holeVertex C) d (.inl w) ht
          simpa only [ContextDecomposition.hole_label C] using h
        let i : Fin k := ⟨d, hd⟩
        by_cases he : w = holeVertex C
        · subst w
          exact ⟨.inl ⟨(0 : Fin (k + 2)), (0 : Fin 1)⟩,
            Or.inr ⟨i, ⟨i, rfl, rfl⟩,
              Or.inl ⟨⟨(0 : Fin (k + 2)), (0 : Fin 1)⟩,
                Or.inr ⟨i, ht, rfl, rfl⟩, True.intro, rfl⟩⟩, rfl⟩
        · let b : BodyVertex C := ⟨w, he⟩
          have hb : (ordinaryPiece C i.succ).Reachable b :=
            ⟨b, Or.inl (Or.inr ⟨i, rfl, ht⟩), .refl⟩
          let q := index (ordinaryPiece C i.succ) ⟨b, hb⟩
          have hq : q ∈ (pieces C i.succ).graph.initial := by
            change (ordinaryPiece C i.succ).initial (vertex (ordinaryPiece C i.succ) q)
            rw [vertex_index]
            exact Or.inr ⟨i, rfl, ht⟩
          refine ⟨.inl ⟨i.succ.succ, q⟩,
            Or.inr ⟨i, ⟨i, rfl, rfl⟩,
              Or.inl ⟨⟨i.succ.succ, q⟩, Or.inl ⟨i, rfl, rfl⟩, hq, rfl⟩⟩, ?_⟩
          change Sum.inl (vertex (ordinaryPiece C i.succ) q).val = .inl w
          rw [vertex_index]
      | succ j =>
        change C.system.graph.edge (vertex (ordinaryPiece C j) u).val d (.inl w) at ht
        by_cases he : w = holeVertex C
        · subst w
          exact ⟨.inl ⟨(0 : Fin (k + 2)), (0 : Fin 1)⟩,
            Or.inr ⟨(0 : Fin 1), ht,
              Or.inl ⟨⟨(0 : Fin (k + 2)), (0 : Fin 1)⟩, ⟨rfl, rfl⟩, True.intro, rfl⟩⟩, rfl⟩
        · let b : BodyVertex C := ⟨w, he⟩
          have hb : (ordinaryPiece C j).Reachable b := by
            obtain ⟨r, hr, hp⟩ := ((index (ordinaryPiece C j)).symm u).property
            exact ⟨r, hr, hp.tail ⟨d, ht⟩⟩
          let q := index (ordinaryPiece C j) ⟨b, hb⟩
          have hq : (pieces C j).graph.edge u d (.inl q) := by
            change (ordinaryPiece C j).edge (vertex (ordinaryPiece C j) u) d
              (.inl (vertex (ordinaryPiece C j) q))
            rw [vertex_index]
            exact ht
          refine ⟨.inl ⟨j.succ, q⟩, Or.inl ⟨q, hq, rfl⟩, ?_⟩
          change Sum.inl (vertex (ordinaryPiece C j) q).val = .inl w
          rw [vertex_index]

private theorem evaluated_pattern {A : RankedSet} (E : SetAlgebra A) {k : ℕ}
    (C : SetContext A k 0) (a : A k) :
    relabel E.eval (pattern C a) = relabel (letterSubstitution a)
      (Lax369799.ExtremalContexts.normalContext (plantedBoundary C) (pieceValue E C)).system := by
  classical
  dsimp only [pattern, relabel, Lax369799.ExtremalContexts.normalContext,
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
conclusion: Lax369799.AlgebraicDecomposition.algebraic_decomposition
---
Flatten a normal pattern labelled by the reachable unary pieces. Its
projection onto the planted original context preserves and lifts all
marks and edges, including the hole's self-loops. Associativity then
replaces each piece by its unary value.
-/
theorem algebraic_decomposition {A : RankedSet} (E : SetAlgebra A) {k : ℕ}
    (C : SetContext A k 0) (a : A k) :
    E.eval 0 (plug (Lax369799.ExtremalContexts.normalContext (plantedBoundary C) (pieceValue E C)) (atomic a)) =
      E.eval 0 (plant (plug C (atomic a))) := by
  let N := Lax369799.ExtremalContexts.normalContext (plantedBoundary C) (pieceValue E C)
  obtain ⟨f, hf⟩ := plug_atomic_cover N a
  obtain ⟨g, hg⟩ := projection_cover C a
  calc
    E.eval 0 (plug N (atomic a)) = E.eval 0 (relabel (letterSubstitution a) N.system) :=
      SumEvaluation.eval_cover E f hf
    _ = E.eval 0 (relabel E.eval (pattern C a)) := congrArg (E.eval 0) (evaluated_pattern E C a).symm
    _ = E.eval 0 (flatten (pattern C a)) := E.associative 0 (pattern C a)
    _ = E.eval 0 (plant (relabel (letterSubstitution a) C.system)) := SumEvaluation.eval_cover E g hg
    _ = E.eval 0 (plant (plug C (atomic a))) := (eval_plant_atomic E C a).symm

end Lax369799Proofs.AlgebraicDecomposition
