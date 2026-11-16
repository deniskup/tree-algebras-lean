import Lax369799.UnaryComposition
import Lax369799Proofs.UntrimmedFlattening
import Mathlib.Tactic.FinCases

namespace Lax369799Proofs.UnaryComposition
set_option backward.isDefEq.respectTransparency false
open Lax369799
open RankedSystems (RankedSet)
open FinitePresentations FiniteSyntacticAlgebra UnaryComposition

private theorem singleton_apply {T : Type} (a b : T) : ({a} : Set T) b ↔ b = a := Iff.rfl

private theorem univ_apply {T : Type} (a : T) : (Set.univ : Set T) a := trivial

/-- Shared simplification at the numeral `1`, also used when elaborating unary chains and graphs. -/
theorem cases_one {k : ℕ} {motive : Fin (k + 2) → Sort _}
    (z : motive 0) (s : ∀ i : Fin (k + 1), motive i.succ) :
    Fin.cases (motive := motive) z s (1 : Fin (k + 2)) = s 0 := rfl

private def triple {A : RankedSet} {n : ℕ} (a b : A 1) (c : A n) :
    FiniteSystem A n where
  size := 3
  graph := {
    label := Fin.cases ⟨1, a⟩ (Fin.cases ⟨1, b⟩ (fun _ => ⟨n, c⟩))
    initial := {0}
    root := ∅
    edge := fun v d t =>
      (v = 0 ∧ d = 0 ∧ t = .inl 1) ∨
      (v = 1 ∧ d = 0 ∧ t = .inl 2) ∨
      (v = 2 ∧ ∃ j : Fin n, d = j.val ∧ t = .inr j)
    direction_valid := by
      rintro v d t (⟨rfl, rfl, _⟩ | ⟨rfl, rfl, _⟩ | ⟨rfl, j, rfl, _⟩)
      · exact Nat.zero_lt_one
      · exact Nat.zero_lt_one
      · exact j.isLt }

private abbrev leftPattern {A : RankedSet} {n : ℕ} (a b : A 1) (c : A n) :=
  application (application a b) (atomic c)

private abbrev rightPattern {A : RankedSet} {n : ℕ} (a b : A 1) (c : A n) :=
  application (atomic a) (application b c)

private abbrev Raw {A : RankedSet} {n : ℕ} (P : FiniteSystem (FiniteSystem A) n) :=
  (v : P.Vertex) × (Inner P.graph v).Vertex

private def leftEquiv {A : RankedSet} {n : ℕ} (a b : A 1) (c : A n) :
    Raw (leftPattern a b c) ≃ Fin 3 where
  toFun := fun v => Fin.cases (fun u => u.castSucc) (fun _ _ => 2) v.1 v.2
  invFun := Fin.cases ⟨(0 : Fin 2), (0 : Fin 2)⟩
    (Fin.cases ⟨(0 : Fin 2), (1 : Fin 2)⟩ (fun _ => ⟨(1 : Fin 2), (0 : Fin 1)⟩))
  left_inv := by rintro ⟨v, u⟩; fin_cases v <;> fin_cases u <;> rfl
  right_inv := by intro v; fin_cases v <;> rfl

private def rightEquiv {A : RankedSet} {n : ℕ} (a b : A 1) (c : A n) :
    Raw (rightPattern a b c) ≃ Fin 3 where
  toFun := fun v => Fin.cases (fun _ => 0) (fun _ u => u.succ) v.1 v.2
  invFun := Fin.cases ⟨(0 : Fin 2), (0 : Fin 1)⟩ (fun u => ⟨(1 : Fin 2), u⟩)
  left_inv := by rintro ⟨v, u⟩; fin_cases v <;> fin_cases u <;> rfl
  right_inv := by intro v; fin_cases v <;> rfl

private def leftIso {A : RankedSet} {n : ℕ} (a b : A 1) (c : A n) :
    PresentationIso (flattenPresentation (leftPattern a b c).graph) (triple a b c).graph where
  vertex := leftEquiv a b c
  label := by rintro ⟨v, u⟩; fin_cases v <;> fin_cases u <;> rfl
  initial := by
    rintro ⟨v, u⟩
    fin_cases v <;> fin_cases u
    · change (0 : Fin 3) = 0 ↔ (0 : Fin 2) = 0 ∧ (0 : Fin 2) = 0
      simp
    · change (1 : Fin 3) = 0 ↔ (0 : Fin 2) = 0 ∧ (1 : Fin 2) = 0
      simp
    · change (2 : Fin 3) = 0 ↔ (1 : Fin 2) = 0 ∧ True
      simp
  root := by
    rintro ⟨v, u⟩
    fin_cases v <;> fin_cases u <;>
      exact ⟨False.elim, fun h => h.elim id (fun h => h.1)⟩
  edge := by
    rintro ⟨v, u⟩ d t
    cases t with
    | inl z =>
      obtain ⟨q, z⟩ := z
      fin_cases v <;> fin_cases u <;> fin_cases q <;> fin_cases z <;>
        simp [leftEquiv, leftPattern, triple, flattenPresentation, Inner, application, atomic,
          ofSetSystem, RankedSystems.atomic, cases_one, singleton_apply, univ_apply, Fin.val_inj, Fin.exists_fin_one, Fin.exists_fin_two]
    | inr j =>
      fin_cases v <;> fin_cases u <;>
        simp [leftEquiv, leftPattern, triple, flattenPresentation, Inner, application, atomic,
          ofSetSystem, RankedSystems.atomic, cases_one, singleton_apply, univ_apply, Fin.val_inj, Fin.exists_fin_one, Fin.exists_fin_two]

private def rightIso {A : RankedSet} {n : ℕ} (a b : A 1) (c : A n) :
    PresentationIso (flattenPresentation (rightPattern a b c).graph) (triple a b c).graph where
  vertex := rightEquiv a b c
  label := by rintro ⟨v, u⟩; fin_cases v <;> fin_cases u <;> rfl
  initial := by
    rintro ⟨v, u⟩
    fin_cases v <;> fin_cases u
    · change (0 : Fin 3) = 0 ↔ (0 : Fin 2) = 0 ∧ True
      simp
    · change (1 : Fin 3) = 0 ↔ (1 : Fin 2) = 0 ∧ (0 : Fin 2) = 0
      simp
    · change (2 : Fin 3) = 0 ↔ (1 : Fin 2) = 0 ∧ (1 : Fin 2) = 0
      simp
  root := by
    rintro ⟨v, u⟩
    fin_cases v <;> fin_cases u <;>
      exact ⟨False.elim, fun h => h.elim id (fun h => h.1)⟩
  edge := by
    rintro ⟨v, u⟩ d t
    cases t with
    | inl z =>
      obtain ⟨q, z⟩ := z
      fin_cases v <;> fin_cases u <;> fin_cases q <;> fin_cases z <;>
        simp [rightEquiv, rightPattern, triple, flattenPresentation, Inner, application, atomic,
          ofSetSystem, RankedSystems.atomic, cases_one, singleton_apply, univ_apply, Fin.val_inj, Fin.exists_fin_one, Fin.exists_fin_two]
    | inr j =>
      fin_cases v <;> fin_cases u <;>
        simp [rightEquiv, rightPattern, triple, flattenPresentation, Inner, application, atomic,
          ofSetSystem, RankedSystems.atomic, cases_one, singleton_apply, univ_apply, Fin.val_inj, Fin.exists_fin_one, Fin.exists_fin_two]

private theorem relabel_application {A B : RankedSet} (f : RankedSystems.RankedMap A B)
    {n : ℕ} (a : A 1) (b : A n) :
    relabel f (application a b) = application (f 1 a) (f n b) := by
  dsimp only [relabel, application]
  congr 1
  congr 1
  funext v
  exact Fin.cases rfl (fun _ => rfl) v

/--
---
conclusion: Lax369799.UnaryComposition.action_law
---
Both bracketings flatten to the same three-vertex chain. Associativity
evaluates the two pieces in either partition before the entire chain.
-/
theorem action_law {A : RankedSet} (E : Algebra A) {n : ℕ}
    (a b : A 1) (c : A n) : act E (product E a b) c = act E a (act E b c) := by
  have hl : Isomorphic (flatten (leftPattern a b c)) (triple a b c) :=
    ⟨UntrimmedFlattening.isoTrans
      (UntrimmedFlattening.isoSymm (UntrimmedFlattening.reindexIso _ (Fintype.equivFin _)))
      (leftIso a b c)⟩
  have hr : Isomorphic (flatten (rightPattern a b c)) (triple a b c) :=
    ⟨UntrimmedFlattening.isoTrans
      (UntrimmedFlattening.isoSymm (UntrimmedFlattening.reindexIso _ (Fintype.equivFin _)))
      (rightIso a b c)⟩
  have hleft := E.associative n (leftPattern a b c)
  have hright := E.associative n (rightPattern a b c)
  rw [relabel_application, E.unit] at hleft hright
  change act E (product E a b) c = _ at hleft
  change act E a (act E b c) = _ at hright
  exact hleft.trans ((E.isomorphic n _ _ hl).trans ((E.isomorphic n _ _ hr).symm.trans hright.symm))

/--
---
conclusion: Lax369799.UnaryComposition.associative
---
The action law in sort one is the semigroup law.
-/
theorem associative {A : RankedSet} (E : Algebra A) (a b c : A 1) :
    product E (product E a b) c = product E a (product E b c) := action_law E a b c

/--
---
conclusion: Lax369799.UnaryComposition.nullary_action
---
In sort zero the second vertex has no exits, giving the terminating-word
application graph.
-/
theorem nullary_action {A : RankedSet} (E : Algebra A) (b : A 1) (a : A 0) :
    act E b a = FiniteBranchWords.act E b a := by
  have h : application b a = FiniteBranchWords.application b a := by
    simp [application, FiniteBranchWords.application]
  exact congrArg (E.eval 0) h

end Lax369799Proofs.UnaryComposition
