import Lax369799.FiniteMarkUnion
import Lax369799.ExpandedSyntacticAlgebra
import Lax369799Proofs.FiniteOuterMorphisms
import Lax369799Proofs.FiniteSums

namespace Lax369799Proofs.FiniteMarkUnion
set_option backward.isDefEq.respectTransparency false
open Lax369799
open RankedSystems (RankedSet Presentation)
open FinitePresentations FiniteSyntacticAlgebra FiniteContextualOrder FiniteAcceptance
open PresentationCovers

private def foldCover {A : RankedSet} {n : ℕ} {V : Type}
    (G H K : Presentation A n V)
    (hl : ∀ v, G.label v = K.label v ∧ H.label v = K.label v)
    (hi : ∀ v, K.initial v ↔ G.initial v ∨ H.initial v)
    (hr : ∀ v, K.root v ↔ G.root v ∨ H.root v)
    (he : ∀ v d t, (G.edge v d t ↔ K.edge v d t) ∧ (H.edge v d t ↔ K.edge v d t)) :
    Cover (sumPresentation G H) K where
  toFun := Sum.elim id id
  label := by intro v; cases v with
              | inl v => exact (hl v).1.symm
              | inr v => exact (hl v).2.symm
  initial := by intro v hv; cases v with
                | inl v => exact (hi v).mpr (Or.inl hv)
                | inr v => exact (hi v).mpr (Or.inr hv)
  root := by intro v hv; cases v with
             | inl v => exact (hr v).mpr (Or.inl hv)
             | inr v => exact (hr v).mpr (Or.inr hv)
  edge := by
    intro v d t ht
    cases v with
    | inl v =>
      obtain ⟨s, hs, rfl⟩ := ht
      have h := (he v d s).1.mp hs
      cases s <;> exact h
    | inr v =>
      obtain ⟨s, hs, rfl⟩ := ht
      have h := (he v d s).2.mp hs
      cases s <;> exact h
  initial_lift := by
    intro v hv
    rcases (hi v).mp hv with h | h
    · exact ⟨.inl v, h, rfl⟩
    · exact ⟨.inr v, h, rfl⟩
  root_lift := by
    intro v hv
    rcases (hr v).mp hv with h | h
    · exact ⟨.inl v, h, rfl⟩
    · exact ⟨.inr v, h, rfl⟩
  edge_lift := by
    intro v d t ht
    cases v with
    | inl v =>
      refine ⟨Sum.map Sum.inl id t, ⟨t, (he v d t).1.mpr ht, rfl⟩, ?_⟩
      cases t <;> rfl
    | inr v =>
      refine ⟨Sum.map Sum.inr id t, ⟨t, (he v d t).2.mpr ht, rfl⟩, ?_⟩
      cases t <;> rfl

/--
---
conclusion: Lax369799.FiniteMarkUnion.evaluation_union
---
Fold two copies of the common graph. The cover is surjective on all
vertices and lifts exactly the union of initial and root marks.
-/
theorem evaluation_union {A : RankedSet} (L : Algebras.Language A)
    (E : ExpandedSyntacticAlgebra.SyntacticAlgebra L) {n : ℕ} {V : Type} [Fintype V]
    (G H K : Presentation (Carrier (Accepting L)) n V)
    (hl : ∀ v, G.label v = K.label v ∧ H.label v = K.label v)
    (hi : ∀ v, K.initial v ↔ G.initial v ∨ H.initial v)
    (hr : ∀ v, K.root v ↔ G.root v ∨ H.root v)
    (he : ∀ v d t, (G.edge v d t ↔ K.edge v d t) ∧ (H.edge v d t ↔ K.edge v d t)) :
    E.algebra.eval n (enumerate K) = sumValue E.algebra
      (E.algebra.eval n (enumerate G)) (E.algebra.eval n (enumerate H)) := by
  classical
  let f := foldCover G H K hl hi hr he
  let eg := Fintype.equivFin V
  let ef := Equiv.sumCongr eg eg
  let gs := sumPresentation (enumerate G).graph (enumerate H).graph
  let rawIso : PresentationIso (sumPresentation G H) gs := {
    vertex := ef
    label := by intro v; cases v <;> simp [ef, gs, enumerate, reindex, sumPresentation, eg, Equiv.sumCongr_apply]
    initial := by intro v; cases v <;> simp [ef, gs, enumerate, reindex, sumPresentation, eg, Equiv.sumCongr_apply]
    root := by intro v; cases v <;> simp [ef, gs, enumerate, reindex, sumPresentation, eg, Equiv.sumCongr_apply]
    edge := by
      intro v d t
      cases v with
      | inl v =>
        constructor
        · rintro ⟨s, hs, heq⟩
          refine ⟨Sum.map eg.symm id s, ?_, ?_⟩
          · simpa [enumerate, reindex, eg] using hs
          · apply (Equiv.sumCongr ef (Equiv.refl _)).injective
            cases s with
            | inl w =>
              change Sum.map ef id t = .inl (.inl (eg (eg.symm w)))
              rw [eg.apply_symm_apply]
              exact heq
            | inr j => exact heq
        · rintro ⟨s, hs, rfl⟩
          refine ⟨Sum.map eg id s, ?_, ?_⟩
          · cases s <;> simpa [enumerate, reindex, eg] using hs
          · cases s <;> rfl
      | inr v =>
        constructor
        · rintro ⟨s, hs, heq⟩
          refine ⟨Sum.map eg.symm id s, ?_, ?_⟩
          · simpa [enumerate, reindex, eg] using hs
          · apply (Equiv.sumCongr ef (Equiv.refl _)).injective
            cases s with
            | inl w =>
              change Sum.map ef id t = .inl (.inr (eg (eg.symm w)))
              rw [eg.apply_symm_apply]
              exact heq
            | inr j => exact heq
        · rintro ⟨s, hs, rfl⟩
          refine ⟨Sum.map eg id s, ?_, ?_⟩
          · cases s <;> simpa [enumerate, reindex, eg] using hs
          · cases s <;> rfl }
  let egs := Fintype.equivFin ((enumerate G).Vertex ⊕ (enumerate H).Vertex)
  let fs := FiniteCovers.compose
    (FiniteCovers.isoCover (UntrimmedFlattening.isoSymm
      (UntrimmedFlattening.isoTrans rawIso (UntrimmedFlattening.reindexIso gs egs))))
    (FiniteCovers.compose f (FiniteCovers.isoCover (UntrimmedFlattening.reindexIso K eg)))
  have hf : Function.Surjective fs.toFun := by
    intro w
    refine ⟨egs (ef (.inl (eg.symm w))), ?_⟩
    change eg (Sum.elim id id (ef.symm (egs.symm (egs (ef (.inl (eg.symm w))))))) = w
    simp
  have hv := FiniteOuterMorphisms.evaluation_cover L E.algebra E.evaluates
    (S := sum (enumerate G) (enumerate H)) (T := enumerate K) fs hf
  have hb := E.algebra.isomorphic n _ _ (FiniteSums.flatten_binary (enumerate G) (enumerate H))
  have hrb : relabel E.algebra.eval (binary (enumerate G) (enumerate H)) =
      binary (E.algebra.eval n (enumerate G)) (E.algebra.eval n (enumerate H)) := by
    dsimp only [relabel, binary]
    congr 1
    congr 1
    funext v
    fin_cases v <;> rfl
  exact hv.symm.trans (hb.symm.trans ((E.algebra.associative n _).symm.trans
    (congrArg (E.algebra.eval n) hrb)))

end Lax369799Proofs.FiniteMarkUnion
