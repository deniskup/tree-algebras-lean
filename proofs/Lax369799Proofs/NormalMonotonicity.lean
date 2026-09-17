import Lax369799Proofs.AlgebraicDecomposition
import Lax369799Proofs.Evaluation

namespace Lax369799Proofs.NormalMonotonicity
open Lax369799.RankedSystems Lax369799.Morphisms Lax369799.Flattening Lax369799.SetAlgebras
open Lax369799.ExtremalContexts
open Lax369799Proofs.AlgebraicDecomposition

private theorem relabel_normal {A B : RankedSet} (f : RankedMap A B) {k : ℕ}
    (D : Boundary k) (m : Fin (k + 1) → A 1) (a : A k) :
    relabel f (relabel (letterSubstitution a) (normalContext D m).system) =
      relabel (letterSubstitution (f k a)) (normalContext D (fun i => f 1 (m i))).system := by
  dsimp only [relabel, normalContext, normalSystem, normalPresentation]
  congr 1
  congr 1
  funext v
  cases v using Fin.cases <;> rfl

private def boundaryMap {A : RankedSet} {k : ℕ} (B D : Boundary k)
    (hr : D.root → B.root) (hl : D.loops ⊆ B.loops) (m : Fin (k + 1) → A 1) (a : A k) :
    Morphism (relabel (letterSubstitution a) (normalContext D m).system)
      (relabel (letterSubstitution a) (normalContext B m).system) where
  toFun := id
  label := fun _ => rfl
  initial := fun _ h => False.elim h
  root := fun v h => h.elim Or.inl (fun h => Or.inr ⟨h.1, hr h.2⟩)
  edge := by
    intro v d t h
    cases t with
    | inr i => exact Fin.elim0 i
    | inl w =>
      cases v using Fin.cases with
      | zero =>
        rcases h with ⟨i, hd, he⟩ | ⟨i, hi, hd, he⟩
        · exact Or.inl ⟨i, hd, he⟩
        · exact Or.inr ⟨i, hl hi, hd, he⟩
      | succ i => exact h

/--
---
conclusion: Lax369799.ExtremalContexts.data_monotone
---
Simultaneous monotonicity changes the unary labels. Adding boundary
marks and self-loops gives a morphism in the opposite direction, so it
also decreases evaluation. Compose these two comparisons.
-/
theorem data_monotone {A : RankedSet} (E : SetAlgebra A) {k : ℕ}
    (x y : Data A k) (h : DataBelow E x y) (a : A k) :
    Below E (E.eval 0 (plug (normalContext x.1 x.2) (atomic a)))
      (E.eval 0 (plug (normalContext y.1 y.2) (atomic a))) := by
  obtain ⟨cx, hcx⟩ := plug_atomic_cover (normalContext x.1 x.2) a
  obtain ⟨cy, hcy⟩ := plug_atomic_cover (normalContext y.1 y.2) a
  rw [SumEvaluation.eval_cover E cx hcx, SumEvaluation.eval_cover E cy hcy]
  let Pairs : RankedSet := fun r => {p : A r × A r // Below E p.1 p.2}
  let fst : RankedMap Pairs A := fun _ p => p.val.1
  let snd : RankedMap Pairs A := fun _ p => p.val.2
  let m : Fin (k + 1) → Pairs 1 := fun i => ⟨(x.2 i, y.2 i), h.2.2 i⟩
  let b : Pairs k := ⟨(a, a), (SetAlgebraTheorems.order_laws E k).1 a⟩
  let P := relabel (letterSubstitution b) (normalContext x.1 m).system
  have hm := Evaluation.relabel_monotone E fst snd (fun _ p => p.property) P
  change Below E (E.eval 0 (relabel fst (relabel (letterSubstitution b) (normalContext x.1 m).system)))
    (E.eval 0 (relabel snd (relabel (letterSubstitution b) (normalContext x.1 m).system))) at hm
  rw [relabel_normal, relabel_normal] at hm
  have hb := E.morphism 0 _ _ ⟨boundaryMap x.1 y.1 h.1 h.2.1 y.2 a⟩
  exact (SetAlgebraTheorems.order_laws E 0).2.2.1 _ _ _ hm hb

end Lax369799Proofs.NormalMonotonicity
