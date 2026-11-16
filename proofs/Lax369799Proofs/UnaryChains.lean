import Lax369799.UnaryChains
import Lax369799Proofs.UnaryComposition
import Lax369799Proofs.SemigroupFactorization
import Lax369799Proofs.FiniteBranchWords
import Lax369799Proofs.UntrimmedFlattening
import Mathlib.Tactic.FinCases

namespace Lax369799Proofs.UnaryChains
set_option backward.isDefEq.respectTransparency false
open Lax369799
open RankedSystems (RankedSet)
open FinitePresentations FiniteSyntacticAlgebra UnaryComposition

open Lax369799.UnaryChains

private theorem path_edge {A : RankedSet} {k n : ℕ} (w : Fin k → A 1) (a : A n)
    (v u : Fin (k + 1)) (d : ℕ) :
    (path w a).graph.edge v d (.inl u) ↔ v.val < k ∧ d = 0 ∧ u.val = v.val + 1 := by
  constructor
  · rintro (⟨i, rfl, rfl, h⟩ | ⟨_, j, _, h⟩)
    · cases h
      exact ⟨i.isLt, rfl, rfl⟩
    · cases h
  · rintro ⟨hv, rfl, hu⟩
    exact Or.inl ⟨⟨v.val, hv⟩, Fin.ext rfl, rfl, congrArg Sum.inl (Fin.ext hu)⟩

private theorem path_variable {A : RankedSet} {k n : ℕ} (w : Fin k → A 1) (a : A n)
    (v : Fin (k + 1)) (d : ℕ) (j : Fin n) :
    (path w a).graph.edge v d (.inr j) ↔ v.val = k ∧ d = j.val := by
  constructor
  · rintro (⟨i, _, _, h⟩ | ⟨rfl, i, rfl, h⟩)
    · cases h
    · cases h
      exact ⟨rfl, rfl⟩
  · rintro ⟨hv, rfl⟩
    exact Or.inr ⟨Fin.ext hv, j, rfl, rfl⟩

private abbrev Raw {A : RankedSet} {k n : ℕ} (w : Fin (k + 1) → A 1) (a : A n) :=
  (v : (application (atomic (w 0)) (path (fun i => w i.succ) a)).Vertex) ×
    (Inner (application (atomic (w 0)) (path (fun i => w i.succ) a)).graph v).Vertex

private def prefixEquiv {A : RankedSet} {k n : ℕ} (w : Fin (k + 1) → A 1) (a : A n) :
    Raw w a ≃ Fin (k + 2) where
  toFun := fun v => Fin.cases (fun _ => 0) (fun _ u => u.succ) v.1 v.2
  invFun := Fin.cases ⟨(0 : Fin 2), (0 : Fin 1)⟩ (fun u => ⟨(1 : Fin 2), u⟩)
  left_inv := by
    rintro ⟨v, u⟩
    fin_cases v
    · fin_cases u; rfl
    · rfl
  right_inv := by intro v; cases v using Fin.cases <;> rfl

private def prefixIso {A : RankedSet} {k n : ℕ} (w : Fin (k + 1) → A 1) (a : A n) :
    PresentationIso (flattenPresentation (application (atomic (w 0)) (path (fun i => w i.succ) a)).graph)
      (path w a).graph where
  vertex := prefixEquiv w a
  label := by
    rintro ⟨v, u⟩
    fin_cases v
    · fin_cases u
      change Fin.lastCases (motive := fun _ => RankedSystems.Symbol A) ⟨n, a⟩ (fun i => ⟨1, w i⟩) (Fin.castSucc (0 : Fin (k + 1))) = _
      exact Fin.lastCases_castSucc (0 : Fin (k + 1))
    · change Fin.lastCases (motive := fun _ => RankedSystems.Symbol A) ⟨n, a⟩ (fun i => ⟨1, w i⟩) u.succ =
        Fin.lastCases (motive := fun _ => RankedSystems.Symbol A) ⟨n, a⟩ (fun i => ⟨1, w i.succ⟩) u
      cases u using Fin.lastCases with
      | last => simp
      | cast i => change Fin.lastCases (motive := fun _ => RankedSystems.Symbol A) _ _ i.succ.castSucc = _; simp only [Fin.lastCases_castSucc]
  initial := by
    rintro ⟨v, u⟩
    fin_cases v
    · fin_cases u; exact ⟨fun _ => ⟨rfl, True.intro⟩, fun _ => rfl⟩
    · change u.succ = 0 ↔ (1 : Fin 2) = 0 ∧ _
      simp
  root := by
    rintro ⟨v, u⟩
    fin_cases v <;> exact ⟨False.elim, fun h => h.elim id (fun h => h.1)⟩
  edge := by
    rintro ⟨v, u⟩ d t
    cases t with
    | inr j =>
      fin_cases v
      · fin_cases u
        change (path w a).graph.edge (0 : Fin (k + 2)) d (.inr j) ↔ _
        rw [path_variable]
        simp [flattenPresentation, Inner, application, atomic, ofSetSystem,
          RankedSystems.atomic, Fin.exists_fin_one]
      · change (path w a).graph.edge u.succ d (.inr j) ↔ _
        rw [path_variable]
        simp [flattenPresentation, Inner, application, atomic, ofSetSystem,
          RankedSystems.atomic, Fin.exists_fin_one, Fin.val_inj,
          Lax369799Proofs.UnaryComposition.cases_one, path_variable]
    | inl z =>
      obtain ⟨q, z⟩ := z
      fin_cases v
      · fin_cases u
        fin_cases q
        · fin_cases z
          change (path w a).graph.edge (0 : Fin (k + 2)) d (.inl (0 : Fin (k + 2))) ↔ _
          rw [path_edge]
          simp [flattenPresentation, Inner, application, atomic, ofSetSystem,
            RankedSystems.atomic, Fin.exists_fin_one]
        · change (path w a).graph.edge (0 : Fin (k + 2)) d (.inl z.succ) ↔ _
          rw [path_edge]
          simp [flattenPresentation, Inner, application, atomic, ofSetSystem,
            RankedSystems.atomic, Fin.exists_fin_one, Fin.exists_fin_two]
          intro _
          change z.val = 0 ↔ z = (0 : Fin (k + 1))
          exact ⟨fun h => Fin.ext h, fun h => congrArg Fin.val h⟩
      · fin_cases q
        · fin_cases z
          change (path w a).graph.edge u.succ d (.inl (0 : Fin (k + 2))) ↔ _
          rw [path_edge]
          simp [flattenPresentation, Inner, application, path]
        · change (path w a).graph.edge u.succ d (.inl z.succ) ↔ _
          rw [path_edge]
          simp [flattenPresentation, Inner, application, path]
          exact (path_edge _ _ u z d).symm

/--
---
conclusion: Lax369799.UnaryChains.evaluation
---
Separate the first vertex by the flattening isomorphism. Associativity
reduces its suffix to a value, and induction gives the word evaluation.
-/
theorem evaluation {A : RankedSet} (E : Algebra A) {k n : ℕ}
    (w : Fin k → A 1) (a : A n) :
    E.eval n (path w a) = (List.ofFn w).foldr (UnaryComposition.act E) a := by
  induction k with
  | zero =>
    have hi : Isomorphic (path w a) (atomic a) := by
      refine ⟨{ vertex := Equiv.refl (Fin 1)
                label := ?_
                initial := ?_
                root := fun _ => Iff.rfl
                edge := ?_ }⟩
      · intro v; fin_cases v
        change (⟨n, a⟩ : RankedSystems.Symbol A) =
          Fin.lastCases ⟨n, a⟩ (fun i => ⟨1, w i⟩) (Fin.last 0)
        exact (Fin.lastCases_last (motive := fun _ : Fin 1 => RankedSystems.Symbol A)
          (last := ⟨n, a⟩) (cast := fun i => ⟨1, w i⟩)).symm
      · intro v; fin_cases v
        exact ⟨fun _ => rfl, fun _ => True.intro⟩
      · intro v d t
        fin_cases v
        simp [path, atomic, ofSetSystem, RankedSystems.atomic]
    simpa using (E.isomorphic _ _ _ hi).trans (E.unit n a)
  | succ k ih =>
    have hi : Isomorphic (flatten (application (atomic (w 0)) (path (fun i => w i.succ) a)))
        (path w a) :=
      ⟨UntrimmedFlattening.isoTrans
        (UntrimmedFlattening.isoSymm (UntrimmedFlattening.reindexIso _ (Fintype.equivFin _)))
        (prefixIso w a)⟩
    have he : relabel E.eval (application (atomic (w 0)) (path (fun i => w i.succ) a)) =
        application (w 0) (E.eval n (path (fun i => w i.succ) a)) := by
      dsimp only [relabel, application]
      congr 1
      congr 1
      funext v
      fin_cases v
      · exact congrArg (Sigma.mk 1) (E.unit 1 (w 0))
      · rfl
    rw [← E.isomorphic _ _ _ hi, ← E.associative, he, ih]
    rw [List.ofFn_succ]
    rfl

private theorem word_list {M : Type} (w : ℕ → M) (i k : ℕ) :
    List.ofFn (fun t : Fin k => w (i + t.val)) ++ [w (i + k)] =
      (List.range' i (k + 1)).map w := by
  induction k generalizing i with
  | zero => simp
  | succ k ih =>
    rw [List.ofFn_succ, List.cons_append, List.range'_succ, List.map_cons]
    congr 1
    simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using ih (i + 1)

private theorem coe_foldr {M : Type} [Semigroup M] (l : List M) (a : M) :
    ((l.foldr (· * ·) a : M) : WithOne M) = (l.map WithOne.coe).prod * (a : WithOne M) := by
  induction l with
  | nil => simp
  | cons b l ih =>
    simp only [List.foldr_cons, List.map_cons, List.prod_cons, WithOne.coe_mul, ih, mul_assoc]

theorem word_label {A : RankedSet} (w : ℕ → A 1) (i k : ℕ) (u : Fin (k + 1)) :
    (word w i k).graph.label u = ⟨1, w (i + u.val)⟩ := by
  cases u using Fin.lastCases with
  | last => simp [word, path]
  | cast u => simp [word, path]

/--
---
conclusion: Lax369799.UnaryChains.word_evaluation
---
The chain evaluation is its right-associated unary product. Associativity
identifies this with the nonempty interval product.
-/
theorem word_evaluation {A : RankedSet} (E : Algebra A) (w : ℕ → A 1) (i k : ℕ) :
    E.eval 1 (word w i k) = UnaryFactorization.block E w i (i + k + 1) := by
  letI : Semigroup (A 1) := { mul := UnaryComposition.product E, mul_assoc := UnaryComposition.associative E }
  apply WithOne.coe_injective
  change (↑(E.eval 1 (word w i k)) : WithOne (A 1)) =
    (↑(Lax369799.SemigroupFactorization.block (M := A 1) w i (i + k + 1)) : WithOne (A 1))
  rw [SemigroupFactorization.coe_block w (by omega : i < i + k + 1)]
  rw [word, evaluation]
  change (((List.ofFn (fun t : Fin k => w (i + t.val))).foldr (· * ·) (w (i + k)) : A 1) :
    WithOne (A 1)) = _
  rw [coe_foldr]
  have hl := congrArg (fun l : List (A 1) => (l.map WithOne.coe).prod) (word_list w i k)
  simpa [Lax369799.WordFactorization.block, List.map_append, List.prod_append,
    List.map_map, Function.comp_def, Nat.add_assoc] using hl

end Lax369799Proofs.UnaryChains
