import Lax369799.ParallelCompression
import Lax369799.DeterministicElements
import Lax369799Proofs.PortReindexing
import Lax369799Proofs.CloneTransitions

namespace Lax369799Proofs.ParallelCompression
set_option backward.isDefEq.respectTransparency false
open Lax369799
open RankedSystems (RankedSet)
open FinitePresentations SetSystemAlgebras FiniteAlgebraMeets CloneTransitions
open Lax369799.PortReindexing

variable {A : RankedSet} {n k : ℕ} (b : Fin (n * k) → A 1)

private def pattern : FiniteSystem (FiniteSystem A) n :=
  ofSetSystem (DeterministicElements.parallel
    (fun i : Fin n => family (fun j : Fin k => b (finProdFinEquiv (i, j)))))

private def rawIso : PresentationIso (flattenPresentation (pattern b).graph)
    (rename (ofSetSystem (DeterministicElements.parallel b)) (fun i => i.divNat)).graph where
  vertex := (Equiv.sigmaEquivProd (Fin n) (Fin k)).trans finProdFinEquiv
  label := fun _ => rfl
  initial := by intro v; exact ⟨fun h => ⟨trivial, trivial⟩, fun h => trivial⟩
  root := by intro v; exact ⟨False.elim, fun h => h.elim id (fun h => h.1)⟩
  edge := by
    intro v d t
    cases t with
    | inl w =>
      change (d = 0 ∧ Sum.inl (finProdFinEquiv (w.1, w.2)) =
        Sum.inr (finProdFinEquiv (v.1, v.2))) ↔ _
      constructor
      · rintro ⟨_, h⟩; cases h
      · rintro (⟨w, h, _⟩ | ⟨i, ⟨j, _, _⟩, (⟨w, h, _, _⟩ | ⟨j, _, h⟩)⟩)
        · obtain ⟨l, _, hh⟩ := h; cases hh
        · cases h.2
        · cases h
    | inr i =>
      change (∃ j, j.divNat = i ∧ d = 0 ∧ Sum.inr j = Sum.inr (finProdFinEquiv (v.1, v.2))) ↔ _
      constructor
      · rintro ⟨j, hj, rfl, he⟩
        have hj' : j = finProdFinEquiv (v.1, v.2) := Sum.inr.inj he
        subst j
        have hv : (finProdFinEquiv (v.1, v.2)).divNat = v.1 :=
          congrArg Prod.fst (finProdFinEquiv.symm_apply_apply (v.1, v.2))
        rw [hv] at hj
        subst i
        exact Or.inr ⟨(0 : Fin 1), ⟨0, rfl, rfl⟩, Or.inr ⟨v.1, ⟨rfl, rfl⟩, rfl⟩⟩
      · rintro (⟨w, h, _⟩ | ⟨j, ⟨l, hd, ht⟩, (⟨w, _, _, h⟩ | ⟨i', hi', he⟩)⟩)
        · obtain ⟨l, _, hh⟩ := h; cases hh
        · cases h
        · have hi : i' = i := Sum.inr.inj he.symm
          subst i'
          obtain ⟨hzero, hvi⟩ := hi'
          have hvi' : i = v.1 := Sum.inr.inj hvi
          subst i
          refine ⟨finProdFinEquiv (v.1, v.2), ?_, ?_, rfl⟩
          · exact congrArg Prod.fst (finProdFinEquiv.symm_apply_apply (v.1, v.2))
          · have hl : l = (0 : Fin 1) := Subsingleton.elim _ _
            exact hd.trans (congrArg Fin.val hl)

/--
---
conclusion: Lax369799.ParallelCompression.evaluation
---
Substitute a finite family of atoms at each parallel component. Flattening
identifies its vertices with the product of directions and copies.
-/
theorem evaluation (E : SetAlgebra A) :
    E.eval n (ofSetSystem (DeterministicElements.parallel (compress E b))) =
      E.eval n (rename (ofSetSystem (DeterministicElements.parallel b)) (fun i => i.divNat)) := by
  have hi : Isomorphic (flatten (pattern b))
      (rename (ofSetSystem (DeterministicElements.parallel b)) (fun i => i.divNat)) :=
    ⟨UntrimmedFlattening.isoTrans
      (UntrimmedFlattening.isoSymm (UntrimmedFlattening.reindexIso _ (Fintype.equivFin _))) (rawIso b)⟩
  have h := (E.associative n (pattern b)).trans (E.isomorphic n _ _ hi)
  exact h

end Lax369799Proofs.ParallelCompression
