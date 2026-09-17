import Lax369799Proofs.RawSystemFlattening
import Lax369799Proofs.ResolutionCompression

set_option backward.isDefEq.respectTransparency false

namespace Lax369799Proofs.CompressionEvaluation
open Lax369799.RankedSystems Lax369799.Renaming Lax369799.Resolutions Lax369799.Algebras
open Lax369799.ResolutionCompression Lax369799Proofs.DeterministicNormalForms
open Lax369799Proofs.Pullbacks

noncomputable def flattenMap {A : RankedSet} {n : ℕ} (T : System (System A) n)
    (arity : T.val.Vertex → ℕ)
    (τ : ∀ v, Fin (T.val.graph.label v).1 → Fin (arity v))
    (sectionMap : ∀ v, Fin (arity v) → Fin (T.val.graph.label v).1) :
    Map (rawFlatten (backPresentation T arity τ sectionMap))
      (rawFlatten (compressedPresentation T arity τ sectionMap)) where
  toFun := fun v => ⟨v.1, by exact v.2⟩
  label := fun _ => rfl
  initial := by intro v h; exact h
  root := by intro v h; exact h
  edge := by
    intro v d t ht
    rcases ht with ⟨w, hw, rfl⟩ | ⟨i, hi, ht⟩
    · obtain ⟨s, hs, he⟩ := hw
      cases s with
      | inl u =>
        have he : w = u := Sum.inl.inj he
        subst w
        exact Or.inl ⟨u, ⟨.inl u, hs, rfl⟩, rfl⟩
      | inr j => cases he
    · obtain ⟨s, hs, he⟩ := hi
      cases s with
      | inl u => cases he
      | inr j =>
        have he : i = sectionMap v.1 (τ v.1 j) := Sum.inr.inj he
        subst i
        refine Or.inr ⟨τ v.1 j, ⟨.inr j, hs, rfl⟩, ?_⟩
        rcases ht with ⟨w, hw, hw', rfl⟩ | ⟨a, ha, rfl⟩
        · exact Or.inl ⟨⟨w.1, by exact w.2⟩, ⟨τ v.1 j, rfl, hw⟩, by exact hw', rfl⟩
        · exact Or.inr ⟨a, ⟨τ v.1 j, rfl, ha⟩, rfl⟩

/--
---
conclusion: Lax369799.ResolutionCompression.evaluation
---
Flattening a component renamed by sectionMap composed with τ maps to the
flattening of the compressed outer pattern. Both are deterministic, so
unfold invariance and associativity identify their evaluations.
-/
theorem evaluation {A : RankedSet} (E : Algebra A) (hE : UnfoldInvariant E) {n : ℕ}
    (T : System (System A) n) (arity : T.val.Vertex → ℕ)
    (τ : ∀ v, Fin (T.val.graph.label v).1 → Fin (arity v))
    (sectionMap : ∀ v, Fin (arity v) → Fin (T.val.graph.label v).1) :
    ∃ U V : System (System A) n,
      U.val = trim (backPresentation T arity τ sectionMap) ∧
      V.val = trim (compressedPresentation T arity τ sectionMap) ∧
      E.eval n (relabelSystem E.eval U) = E.eval n (relabelSystem E.eval V) := by
  let G := backPresentation T arity τ sectionMap
  let H := compressedPresentation T arity τ sectionMap
  obtain ⟨r, hr⟩ := T.property.1
  have hG : ∀ v d, d < (G.label v).1 → ∃! t, G.edge v d t := T.property.2.2
  have hH : ∀ v d, d < (H.label v).1 → ∃! t, H.edge v d t := by
    intro v d hd
    obtain ⟨t, ht, hu⟩ := T.property.2.2 v (sectionMap v ⟨d, hd⟩).val (sectionMap v ⟨d, hd⟩).isLt
    refine ⟨t, ⟨⟨d, hd⟩, rfl, ht⟩, ?_⟩
    rintro u ⟨i, hi, hh⟩
    have he : i = ⟨d, hd⟩ := Fin.ext hi.symm
    subst i
    exact hu u hh
  let U : System (System A) n := ⟨trim G, Yields.trim_deterministic G r hr T.property.2.1 hG⟩
  let V : System (System A) n := ⟨trim H, Yields.trim_deterministic H r hr T.property.2.1 hH⟩
  let U' : System A n := ⟨trim (rawFlatten G), RawSystemFlattening.deterministic G r hr T.property.2.1 hG⟩
  let V' : System A n := ⟨trim (rawFlatten H), RawSystemFlattening.deterministic H r hr T.property.2.1 hH⟩
  let f : Lax369799.Morphisms.Morphism U'.val V'.val := trimMap (flattenMap T arity τ sectionMap)
  have he := hE n U' V' ⟨U'.val,
    ⟨MorphismTheorems.identity _, MorphismTheorems.identity_surjective _⟩,
    ⟨f, MorphismTheorems.system_morphism_locally_surjective U' V' f⟩⟩
  refine ⟨U, V, rfl, rfl, ?_⟩
  exact (RawSystemFlattening.evaluation E hE G r hr T.property.2.1 hG).trans
    (he.trans (RawSystemFlattening.evaluation E hE H r hr T.property.2.1 hH).symm)

end Lax369799Proofs.CompressionEvaluation
