import Lax369799.BranchMonotonicity
import Lax369799Proofs.SetSystemAlgebras
import Lax369799Proofs.AlgebraicOmegaWords
import Lax369799Proofs.UnaryChains

namespace Lax369799Proofs.BranchMonotonicity
set_option backward.isDefEq.respectTransparency false
open Lax369799
open RankedSystems (RankedSet)
open FinitePresentations SetSystemAlgebras UnaryComposition UnaryFactorization

/--
---
conclusion: Lax369799.BranchMonotonicity.act_mono
---
-/
theorem act_mono {A : RankedSet} (E : SetAlgebra A) {n : ℕ}
    {a a' : A 1} {b b' : A n} (ha : Below E a a') (hb : Below E b b') :
    Below E (act E.toAlgebra a b) (act E.toAlgebra a' b') := by
  let P := application a b
  let q : ∀ i : Fin 2, A (P.graph.label i).1 := Fin.cases a' (fun _ => b')
  have h := SetSystemAlgebras.evaluation_monotone E P (fun i => (P.graph.label i).2) q
    (fun i => Fin.cases ha (fun _ => hb) i)
  have hq : withLabels P q = application a' b' := by
    unfold withLabels P application
    congr 1
    congr 1
    funext i
    exact Fin.cases rfl (fun _ => rfl) i
  rw [hq] at h
  exact h

/--
---
conclusion: Lax369799.BranchMonotonicity.product_mono
---
-/
theorem product_mono {A : RankedSet} (E : SetAlgebra A)
    {a a' b b' : A 1} (ha : Below E a a') (hb : Below E b b') :
    Below E (product E.toAlgebra a b) (product E.toAlgebra a' b') := act_mono E ha hb

/--
---
conclusion: Lax369799.BranchMonotonicity.block_mono
---
-/
theorem block_mono {A : RankedSet} (E : SetAlgebra A)
    (w v : ℕ → A 1) (h : ∀ i, Below E (w i) (v i)) (i j : ℕ) :
    Below E (block E.toAlgebra w i j) (block E.toAlgebra v i j) := by
  have go (l : List ℕ) {a b : A 1} (hab : Below E a b) :
      Below E ((l.map w).foldl (product E.toAlgebra) a)
        ((l.map v).foldl (product E.toAlgebra) b) := by
    induction l generalizing a b with
    | nil => exact hab
    | cons x xs ih => exact ih (product_mono E hab (h x))
  exact go _ (h i)

/--
---
conclusion: Lax369799.BranchMonotonicity.finite_mono
---
-/
theorem finite_mono {A : RankedSet} (E : SetAlgebra A)
    {w v : List (A 1)} (h : List.Forall₂ (Below E) w v)
    {a b : A 0} (hab : Below E a b) :
    Below E (FiniteBranchWords.value E.toAlgebra w a)
      (FiniteBranchWords.value E.toAlgebra v b) := by
  induction h with
  | nil => exact hab
  | @cons x y xs ys hxy _ ih =>
    change Below E (FiniteBranchWords.act E.toAlgebra x _)
      (FiniteBranchWords.act E.toAlgebra y _)
    rw [← UnaryComposition.nullary_action, ← UnaryComposition.nullary_action]
    exact act_mono E hxy ih

/--
---
conclusion: Lax369799.BranchMonotonicity.block_append
---
-/
theorem block_append {A : RankedSet} (E : FiniteSyntacticAlgebra.Algebra A)
    (w : ℕ → A 1) {i j k : ℕ} (hij : i < j) (hjk : j < k) :
    block E w i k = product E (block E w i j) (block E w j k) := by
  letI : Semigroup (A 1) := { mul := product E, mul_assoc := UnaryComposition.associative E }
  apply WithOne.coe_injective (α := A 1)
  change (↑(block E w i k) : WithOne (A 1)) = ↑((block E w i j) * (block E w j k))
  have coeBlock {s t : ℕ} (hst : s < t) :
      (↑(block E w s t) : WithOne (A 1)) =
        WordFactorization.block (fun n => (w n : WithOne (A 1))) s t :=
    SemigroupFactorization.coe_block w hst
  rw [WithOne.coe_mul, coeBlock (hij.trans hjk), coeBlock hij, coeBlock hjk]
  exact WordFactorization.block_append _ hij.le hjk.le

/--
---
conclusion: Lax369799.BranchMonotonicity.lasso_mono
---
-/
theorem lasso_mono {A : RankedSet} (E : SetAlgebra A)
    {a a' e e' : A 1} (ha : Below E a a') (he : Below E e e') :
    Below E (E.eval 0 (lasso a e)) (E.eval 0 (lasso a' e')) := by
  let P := lasso a e
  let q : ∀ i : Fin 2, A (P.graph.label i).1 := Fin.cases a' (fun _ => e')
  have h := SetSystemAlgebras.evaluation_monotone E P (fun i => (P.graph.label i).2) q
    (fun i => Fin.cases ha (fun _ => he) i)
  have hq : withLabels P q = lasso a' e' := by
    unfold withLabels P lasso
    congr 1
    congr 1
    funext i
    exact Fin.cases rfl (fun _ => rfl) i
  rw [hq] at h
  exact h

/--
---
conclusion: Lax369799.BranchMonotonicity.infinite_mono
---
-/
theorem infinite_mono {A : RankedSet} (E : SetAlgebra A) [Finite (A 1)]
    (F : Set (A 0)) (hF : ∀ a b, a ∈ F → Below E a b → b ∈ F)
    (w v : ℕ → A 1) (h : ∀ i, Below E (w i) (v i))
    (hw : AlgebraicOmegaWords.Accepts E.toAlgebra F w) :
    AlgebraicOmegaWords.Accepts E.toAlgebra F v := by
  obtain ⟨a, e, c, _, hacc, hee, hae, hc, hpos, _, hp, hb⟩ :=
    AlgebraicOmegaWords.recurrent_factorization E.toAlgebra F w (fun _ => ()) hw
  obtain ⟨f, t, hf, ht⟩ := InfiniteRamsey.pairs
    (fun i j => (block E.toAlgebra v (c i) (c j), block E.toAlgebra v 0 (c i)))
  let d := c ∘ f
  have hd : StrictMono d := hc.comp hf
  have hdpos : 0 < d 0 := hpos.trans_le (hc.monotone (Nat.zero_le _))
  have hprefix (i) : block E.toAlgebra v 0 (d i) = t.2 :=
    congrArg Prod.snd (ht i (i + 1) (by omega))
  have hblock (i j) (hij : i < j) : block E.toAlgebra v (d i) (d j) = t.1 :=
    congrArg Prod.fst (ht i j hij)
  have hstable := block_append E.toAlgebra v hdpos (hd (by decide : 0 < 1))
  rw [hprefix 0, hprefix 1, hblock 0 1 (by decide)] at hstable
  have hidem := block_append E.toAlgebra v (hd (by decide : 0 < 1)) (hd (by decide : 1 < 2))
  rw [hblock 0 2 (by decide), hblock 0 1 (by decide), hblock 1 2 (by decide)] at hidem
  have ha : Below E a t.2 := by
    have hm := block_mono E w v h 0 (d 0)
    rw [hprefix 0] at hm
    change Below E (block E.toAlgebra w 0 (c (f 0))) t.2 at hm
    rw [hp] at hm
    exact hm
  have he : Below E e t.1 := by
    have hm := block_mono E w v h (d 0) (d 1)
    rw [hblock 0 1 (by decide)] at hm
    change Below E (block E.toAlgebra w (c (f 0)) (c (f 1))) t.1 at hm
    rw [hb _ _ (hf (by decide : 0 < 1))] at hm
    exact hm
  exact ⟨t.2, t.1, d, hF _ _ hacc (lasso_mono E ha he), hidem.symm, hstable.symm,
    hd, hdpos, hprefix 0, fun i => hblock i (i + 1) (by omega)⟩

/--
---
conclusion: Lax369799.BranchMonotonicity.condition
---
Transport the algebraic comparisons through the specification of the
finite and infinite word conditions.
-/
theorem condition {A : RankedSet} (E : SetAlgebra A) [Fintype (A 1)] [Fintype (A 0)]
    (F : Set (A 0)) (hF : ∀ a b, a ∈ F → Below E a b → b ∈ F)
    (D : UnfoldAutomata.WordCondition (Fintype.card (A 1)) (Fintype.card (A 0)))
    (hD : (∀ w a, D.AcceptsFinite w a ↔
      FiniteBranchWords.value E.toAlgebra (w.map (Fintype.equivFin (A 1)).symm)
        ((Fintype.equivFin (A 0)).symm a) ∈ F) ∧
      (∀ w, D.AcceptsInfinite w ↔ AlgebraicOmegaWords.Accepts E.toAlgebra F
        (fun n => (Fintype.equivFin (A 1)).symm (w n)))) :
    Lax369799.BranchMonotonicity.ConditionMonotone E D := by
  constructor
  · intro w v a b h hv ha
    apply (hD.1 _ _).mpr
    have hmap : List.Forall₂ (Below E)
        (w.map (Fintype.equivFin (A 1)).symm) (v.map (Fintype.equivFin (A 1)).symm) := by
      clear ha
      induction h with
      | nil => exact .nil
      | cons hxy _ ih => exact .cons hxy ih
    exact hF _ _ ((hD.1 _ _).mp ha) (finite_mono E hmap hv)
  · intro w v h hw
    exact (hD.2 _).mpr (infinite_mono E F hF _ _ h ((hD.2 _).mp hw))

end Lax369799Proofs.BranchMonotonicity
