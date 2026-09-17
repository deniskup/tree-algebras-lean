import Lax369799.MorphismTheorems

namespace Lax369799Proofs.MorphismTheorems
open Lax369799.RankedSystems Lax369799.Morphisms

def identity {A : RankedSet} {n : ℕ} (S : SetSystem A n) : Morphism S S where
  toFun := id
  initial := fun _ h => h
  root := fun _ h => h
  label := fun _ => rfl
  edge := by intro v d t h; cases t <;> exact h

theorem identity_surjective {A : RankedSet} {n : ℕ} (S : SetSystem A n) :
    (identity S).LocallySurjective := by
  refine ⟨?_, ?_, ?_⟩
  · intro v hv; exact ⟨v, hv, rfl⟩
  · intro v hv; exact ⟨v, hv, rfl⟩
  · intro v d t ht
    refine ⟨t, ht, ?_⟩
    cases t <;> rfl

def compose {A : RankedSet} {n : ℕ} {S T U : SetSystem A n}
    (f : Morphism S T) (g : Morphism T U) : Morphism S U where
  toFun := g.toFun ∘ f.toFun
  initial := fun v h => g.initial _ (f.initial v h)
  root := fun v h => g.root _ (f.root v h)
  label := fun v => (g.label _).trans (f.label v)
  edge := by
    intro v d t h
    have h' := g.edge _ d _ (f.edge v d t h)
    cases t <;> exact h'

/--
---
conclusion: Lax369799.MorphismTheorems.composition
---
Successively lift initial vertices, roots, and outgoing edges through the
two maps. Their composite preserves all the defining data.
-/
theorem composition {A : RankedSet} {n : ℕ} {S T U : SetSystem A n}
    (f : Morphism S T) (g : Morphism T U) :
    ∃ h : Morphism S U, h.toFun = g.toFun ∘ f.toFun ∧
      (f.LocallySurjective → g.LocallySurjective → h.LocallySurjective) := by
  refine ⟨compose f g, rfl, ?_⟩
  intro hf hg
  refine ⟨?_, ?_, ?_⟩
  · intro w hw
    obtain ⟨v, hv, rfl⟩ := hg.1 w hw
    obtain ⟨u, hu, rfl⟩ := hf.1 v hv
    exact ⟨u, hu, rfl⟩
  · intro w hw
    obtain ⟨v, hv, rfl⟩ := hg.2.1 w hw
    obtain ⟨u, hu, rfl⟩ := hf.2.1 v hv
    exact ⟨u, hu, rfl⟩
  · intro v d t ht
    obtain ⟨s, hs, he⟩ := hg.2.2 (f.toFun v) d t ht
    obtain ⟨r, hr, hf⟩ := hf.2.2 v d s hs
    refine ⟨r, hr, ?_⟩
    rw [← hf] at he
    cases r <;> exact he

/--
---
conclusion: Lax369799.MorphismTheorems.system_morphism_locally_surjective
---
A system has a unique initial vertex and a unique successor in each
available direction. Preservation therefore implies local surjectivity.
-/
theorem system_morphism_locally_surjective {A : RankedSet} {n : ℕ}
    (S T : System A n) (f : Morphism S.val T.val) : f.LocallySurjective := by
  refine ⟨?_, ?_, ?_⟩
  · intro w hw
    obtain ⟨v, hv⟩ := S.property.1
    obtain ⟨u, hu⟩ := T.property.1
    have hvi : v ∈ S.val.graph.initial := by rw [hv]; exact Set.mem_singleton v
    have hfi := f.initial v hvi
    rw [hu] at hw hfi
    exact ⟨v, hvi, hfi.trans hw.symm⟩
  · intro w hw
    rw [T.property.2.1] at hw
    exact False.elim hw
  · intro v d t ht
    have hd := T.val.graph.direction_valid (f.toFun v) d t ht
    have hs : d < (S.val.graph.label v).1 := by rw [f.label v] at hd; exact hd
    obtain ⟨s, hs, _⟩ := S.property.2.2 v d hs
    refine ⟨s, hs, ?_⟩
    exact (T.property.2.2 (f.toFun v) d hd).unique (f.edge v d s hs) ht

end Lax369799Proofs.MorphismTheorems
