import Lax369799.SetSystemAlgebras
import Lax369799.AlgebraicOmegaWords

/-!
---
title: Monotonicity of algebraic branch conditions
type: theorem
---
Unary application and finite branch evaluation are monotone. For a finite
unary sort, increasing every letter of an accepted infinite word also
preserves acceptance. A common subsequence of factorization cuts compares
the accepting linked pairs. These comparisons underlie the rerouting
construction of Lemma 108.
-/
namespace Lax369799.BranchMonotonicity
open RankedSystems (RankedSet)
open FinitePresentations SetSystemAlgebras UnaryComposition UnaryFactorization

def ConditionMonotone {A : RankedSet} (E : SetAlgebra A)
    [Fintype (A 1)] [Fintype (A 0)]
    (D : UnfoldAutomata.WordCondition (Fintype.card (A 1)) (Fintype.card (A 0))) : Prop :=
  (∀ w v a b, List.Forall₂ (fun x y => Below E
      ((Fintype.equivFin (A 1)).symm x) ((Fintype.equivFin (A 1)).symm y)) w v →
    Below E ((Fintype.equivFin (A 0)).symm a) ((Fintype.equivFin (A 0)).symm b) →
    D.AcceptsFinite w a → D.AcceptsFinite v b) ∧
  (∀ w v, (∀ i, Below E ((Fintype.equivFin (A 1)).symm (w i))
      ((Fintype.equivFin (A 1)).symm (v i))) →
    D.AcceptsInfinite w → D.AcceptsInfinite v)

axiom condition {A : RankedSet} (E : SetAlgebra A) [Fintype (A 1)] [Fintype (A 0)]
    (F : Set (A 0)) (hF : ∀ a b, a ∈ F → Below E a b → b ∈ F)
    (D : UnfoldAutomata.WordCondition (Fintype.card (A 1)) (Fintype.card (A 0)))
    (hD : (∀ w a, D.AcceptsFinite w a ↔
      FiniteBranchWords.value E.toAlgebra (w.map (Fintype.equivFin (A 1)).symm)
        ((Fintype.equivFin (A 0)).symm a) ∈ F) ∧
      (∀ w, D.AcceptsInfinite w ↔ AlgebraicOmegaWords.Accepts E.toAlgebra F
        (fun n => (Fintype.equivFin (A 1)).symm (w n)))) : ConditionMonotone E D

axiom act_mono {A : RankedSet} (E : SetAlgebra A) {n : ℕ}
    {a a' : A 1} {b b' : A n} (ha : Below E a a') (hb : Below E b b') :
    Below E (act E.toAlgebra a b) (act E.toAlgebra a' b')

axiom product_mono {A : RankedSet} (E : SetAlgebra A)
    {a a' b b' : A 1} (ha : Below E a a') (hb : Below E b b') :
    Below E (product E.toAlgebra a b) (product E.toAlgebra a' b')

axiom block_mono {A : RankedSet} (E : SetAlgebra A)
    (w v : ℕ → A 1) (h : ∀ i, Below E (w i) (v i)) (i j : ℕ) :
    Below E (block E.toAlgebra w i j) (block E.toAlgebra v i j)

axiom finite_mono {A : RankedSet} (E : SetAlgebra A)
    {w v : List (A 1)} (h : List.Forall₂ (Below E) w v)
    {a b : A 0} (hab : Below E a b) :
    Below E (FiniteBranchWords.value E.toAlgebra w a)
      (FiniteBranchWords.value E.toAlgebra v b)

axiom block_append {A : RankedSet} (E : FiniteSyntacticAlgebra.Algebra A)
    (w : ℕ → A 1) {i j k : ℕ} (hij : i < j) (hjk : j < k) :
    block E w i k = product E (block E w i j) (block E w j k)

axiom lasso_mono {A : RankedSet} (E : SetAlgebra A)
    {a a' e e' : A 1} (ha : Below E a a') (he : Below E e e') :
    Below E (E.eval 0 (lasso a e)) (E.eval 0 (lasso a' e'))

axiom infinite_mono {A : RankedSet} (E : SetAlgebra A) [Finite (A 1)]
    (F : Set (A 0)) (hF : ∀ a b, a ∈ F → Below E a b → b ∈ F)
    (w v : ℕ → A 1) (h : ∀ i, Below E (w i) (v i))
    (hw : AlgebraicOmegaWords.Accepts E.toAlgebra F w) :
    AlgebraicOmegaWords.Accepts E.toAlgebra F v

end Lax369799.BranchMonotonicity
