import Lax369799.CloneRunRefinement
import Lax369799Proofs.CloneTransitions
import Mathlib.Data.List.Forall2
import Lax369799Proofs.DirectionReindexing
import Lax369799Proofs.BranchMonotonicity

namespace Lax369799Proofs.ReindexedRuns
set_option backward.isDefEq.respectTransparency false
open Lax369799
open RankedSystems (RankedSet System)
open TransitionEncoding UnfoldAutomata SetSystemAlgebras
open Lax369799.DirectionReindexing

variable {P : Type} (S : System (TransitionAlphabet P) 0) (R : Reindexing S)

def finiteBranch {k : ℕ} (b : FiniteBranch (DirectionReindexing.system S R) k) :
    FiniteBranch S k where
  vertex := b.vertex
  direction := fun i => R.map (b.vertex i.castSucc) (b.direction i)
  starts := b.starts
  follows := by
    intro i
    obtain ⟨j, hj, he⟩ := b.follows i
    have hj' : j = b.direction i := Fin.ext hj.symm
    subst j
    exact he
  ends := (DirectionReindexing.zero_iff S R _).mp b.ends

def infiniteBranch (b : InfiniteBranch (DirectionReindexing.system S R)) :
    InfiniteBranch S where
  vertex := b.vertex
  direction := fun i => R.map (b.vertex i) (b.direction i)
  starts := b.starts
  follows := by
    intro i
    obtain ⟨j, hj, he⟩ := b.follows i
    have hj' : j = b.direction i := Fin.ext hj.symm
    subst j
    exact he

theorem accepting {Y : RankedSet} (E : SetAlgebra Y)
    [Fintype (Y 1)] [Fintype (Y 0)]
    (D : WordCondition (Fintype.card (Y 1)) (Fintype.card (Y 0)))
    (hD : Lax369799.BranchMonotonicity.ConditionMonotone E D)
    (r : Labelling (Fintype.card (Y 1)) (Fintype.card (Y 0)) S)
    (s : Labelling (Fintype.card (Y 1)) (Fintype.card (Y 0)) (DirectionReindexing.system S R))
    (he : ∀ v i, Below E ((Fintype.equivFin (Y 1)).symm (r.edgeType v (R.map v i)))
      ((Fintype.equivFin (Y 1)).symm (s.edgeType v i)))
    (hz : ∀ v (h : R.arity v = 0), Below E
      ((Fintype.equivFin (Y 0)).symm (r.leafType v ((DirectionReindexing.zero_iff S R v).mp h)))
      ((Fintype.equivFin (Y 0)).symm (s.leafType v h)))
    (hr : r.Accepting D) : s.Accepting D := by
  constructor
  · intro k b
    apply hD.1 _ _ _ _ ?_ (hz _ b.ends) (hr.1 k (finiteBranch S R b))
    apply List.forall₂_of_length_eq_of_get (by simp)
    intro i hi hj
    simpa only [List.get_eq_getElem, List.getElem_ofFn, Labelling.asRun, finiteBranch] using
      he (b.vertex (⟨i, by simpa using hi⟩ : Fin k).castSucc)
        (b.direction (⟨i, by simpa using hi⟩ : Fin k))
  · intro b
    exact hD.2 _ _ (fun i => he _ _) (hr.2 (infiniteBranch S R b))

end Lax369799Proofs.ReindexedRuns

namespace Lax369799Proofs.CloneRunRefinement
set_option backward.isDefEq.respectTransparency false
open Lax369799
open RankedSystems (RankedSet System)
open TransitionEncoding UnfoldAutomata SetSystemAlgebras
open Lax369799.DirectionReindexing

open Lax369799.CloneRunRefinement

variable {P : Type} {Y : RankedSet} (E : SetAlgebra Y)
    [Fintype (Y 1)] [Fintype (Y 0)]
    (T : Set P → ∀ n, Set (Fin (n + 1) → Y 1))
    (leaves : Set P → Set (Fin (Fintype.card (Y 0))))
    (D : WordCondition (Fintype.card (Y 1)) (Fintype.card (Y 0)))
    (S : System (TransitionAlphabet P) 0)
    (r : Run (CloneTransitions.automaton (CloneTransitions.beta E T) leaves D) S)

private structure At (v : S.val.Vertex) where
  arity : ℕ
  map : Fin arity → Fin (Rank S v)
  surjective : Function.Surjective map
  label : Fin arity → Y 1
  increases : ∀ i, Below E ((Fintype.equivFin (Y 1)).symm (r.edgeType v (map i))) (label i)
  legal : ∀ n (h : arity = n + 1), (fun i => label (Fin.cast h.symm i)) ∈ T (S.val.graph.label v).2 n

private theorem valuation_cast {P : Type} {n m : ℕ} (h : n = m)
    (ν : TransitionAlphabet P n) : (h ▸ ν : TransitionAlphabet P m) = ν := by
  cases h
  rfl

private theorem at_exists (v : S.val.Vertex) : Nonempty (At E T leaves D S r v) := by
  classical
  by_cases hv : Rank S v = 0
  · refine ⟨{ arity := 0
              map := Fin.elim0
              surjective := ?_
              label := Fin.elim0
              increases := fun i => nomatch i
              legal := ?_ }⟩
    · intro i
      have := i.isLt
      omega
    · intro n h
      omega
  · obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero hv
    have ht := r.transitions v n hn
    simp only [CloneTransitions.automaton, valuation_cast] at ht
    change (fun i => (Fintype.equivFin (Y 1)).symm (r.edgeType v (Fin.cast hn.symm i))) ∈
      CloneTransitions.Closure (CloneTransitions.beta E T (S.val.graph.label v).2) (n + 1) at ht
    obtain ⟨l, c, hc, σ, hσ, hm⟩ := CloneTransitions.refinement E T _ _ ht
    refine ⟨{ arity := l + 1
              map := fun i => Fin.cast hn.symm (σ i)
              surjective := ?_
              label := c
              increases := hm
              legal := ?_ }⟩
    · intro i
      obtain ⟨j, hj⟩ := hσ (Fin.cast hn i)
      exact ⟨j, by dsimp only; rw [hj]; exact Fin.ext rfl⟩
    · intro k hk
      have hkl : l = k := Nat.succ.inj hk
      subst k
      simpa only [Fin.cast_refl, id_eq] using hc

/--
---
conclusion: Lax369799.CloneRunRefinement.run_refinement
---
Apply local refinement at every nonleaf vertex and preserve the leaves.
The surjective direction maps preserve the decoded system, and every
branch projects to one with smaller labels in the original clone run.
-/
theorem run_refinement
    (hD : Lax369799.BranchMonotonicity.ConditionMonotone E D) (hr : r.Accepting) :
    ∃ U : System (TransitionAlphabet P) 0, Isomorphic (decode U) (decode S) ∧
      ∃ s : Run (fromTable T leaves D) U, s.Accepting := by
  classical
  let a := fun v => Classical.choice (at_exists E T leaves D S r v)
  let R : Reindexing S := ⟨fun v => (a v).arity, fun v => (a v).map, fun v => (a v).surjective⟩
  let U := DirectionReindexing.system S R
  let s : Run (fromTable T leaves D) U := {
    edgeType := fun v i => (Fintype.equivFin (Y 1)) ((a v).label i)
    leafType := fun v h => r.leafType v ((DirectionReindexing.zero_iff S R v).mp h)
    transitions := by
      intro v k h
      simp only [fromTable, valuation_cast, Equiv.symm_apply_apply]
      change (fun i => (Fintype.equivFin (Y 1)).symm
        ((Fintype.equivFin (Y 1)) ((a v).label (Fin.cast h.symm i)))) ∈ T (S.val.graph.label v).2 k
      simpa only [Equiv.symm_apply_apply] using (a v).legal k h
    leaves := by
      intro v h
      have hl := r.leaves v ((DirectionReindexing.zero_iff S R v).mp h)
      simp only [fromTable, CloneTransitions.automaton, valuation_cast] at hl ⊢
      exact hl }
  refine ⟨U, DirectionReindexing.decode_isomorphic R (DirectionReindexing.realizes S R), s, ?_⟩
  apply ReindexedRuns.accepting S R E D hD r.toLabelling s.toLabelling ?_ ?_ hr
  · intro v i
    change Below E ((Fintype.equivFin (Y 1)).symm (r.edgeType v ((a v).map i)))
      ((Fintype.equivFin (Y 1)).symm ((Fintype.equivFin (Y 1)) ((a v).label i)))
    rw [Equiv.symm_apply_apply]
    exact (a v).increases i
  · intro v h
    exact (SetSystemAlgebras.order_laws E 0).1 _

end Lax369799Proofs.CloneRunRefinement
