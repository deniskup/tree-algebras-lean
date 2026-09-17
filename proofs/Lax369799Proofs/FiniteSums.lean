import Lax369799Proofs.UntrimmedFlattening
import Mathlib.Tactic.FinCases

namespace Lax369799Proofs.FiniteSums
open Lax369799.RankedSystems (RankedSet)
open Lax369799.FinitePresentations
open Lax369799Proofs.UntrimmedFlattening

private def split {A : RankedSet} {n : ℕ} (S T : FiniteSystem A n) :
    ((v : (binary S T).Vertex) × (Inner (binary S T).graph v).Vertex) ≃ S.Vertex ⊕ T.Vertex where
  toFun := fun v => Fin.cases (fun w => .inl w) (fun _ w => .inr w) v.1 v.2
  invFun := Sum.elim (fun v => ⟨(0 : Fin 2), v⟩) (fun v => ⟨(1 : Fin 2), v⟩)
  left_inv := by rintro ⟨v, w⟩; fin_cases v <;> rfl
  right_inv := by intro v; cases v <;> rfl

private def binaryIso {A : RankedSet} {n : ℕ} (S T : FiniteSystem A n) :
    PresentationIso (flattenPresentation (binary S T).graph) (sumPresentation S.graph T.graph) where
  vertex := split S T
  label := by rintro ⟨v, w⟩; fin_cases v <;> rfl
  initial := by
    rintro ⟨v, w⟩
    fin_cases v <;> exact ⟨fun h => ⟨True.intro, h⟩, fun h => h.2⟩
  root := by
    rintro ⟨v, w⟩
    fin_cases v <;> exact ⟨Or.inl, fun h => h.elim id (fun h => False.elim h.1)⟩
  edge := by
    rintro ⟨v, w⟩ d t
    fin_cases v
    all_goals
      constructor
      · rintro ⟨s, hs, he⟩
        cases s with
        | inl u =>
          first
          | have ht : t = .inl ⟨(0 : Fin 2), u⟩ := by
              apply (Equiv.sumCongr (split S T) (Equiv.refl _)).injective
              exact he
            subst t
            exact Or.inl ⟨u, hs, rfl⟩
          | have ht : t = .inl ⟨(1 : Fin 2), u⟩ := by
              apply (Equiv.sumCongr (split S T) (Equiv.refl _)).injective
              exact he
            subst t
            exact Or.inl ⟨u, hs, rfl⟩
        | inr i =>
          have ht : t = .inr i := by
            apply (Equiv.sumCongr (split S T) (Equiv.refl _)).injective
            exact he
          subst t
          exact Or.inr ⟨i, hs, Or.inr ⟨i, ⟨i, rfl, rfl⟩, rfl⟩⟩
      · intro h
        rcases h with ⟨u, hu, rfl⟩ | ⟨i, hi, h⟩
        · exact ⟨.inl u, hu, rfl⟩
        · rcases h with ⟨u, ⟨j, _, he⟩, _⟩ | ⟨j, ⟨l, hl, he⟩, rfl⟩
          · cases he
          · have hj := Sum.inr.inj he
            have hi' : i = l := Fin.ext hl
            subst j
            subst i
            exact ⟨.inr l, hi, rfl⟩

/--
---
conclusion: Lax369799.FinitePresentations.flatten_binary
---
The two outer vertices select the two disjoint summands. Their inner
vertices are retained without pruning, and the coordinate correspondence
preserves and reflects every mark and edge.
-/
theorem flatten_binary {A : RankedSet} {n : ℕ} (S T : FiniteSystem A n) :
    Isomorphic (flatten (binary S T)) (sum S T) := by
  classical
  exact ⟨isoTrans (isoSymm (reindexIso _ (Fintype.equivFin _)))
    (isoTrans (binaryIso S T) (reindexIso _ (Fintype.equivFin _)))⟩

end Lax369799Proofs.FiniteSums
