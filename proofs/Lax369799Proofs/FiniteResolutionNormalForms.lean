import Lax369799.FiniteResolutionNormalForms
import Lax369799Proofs.ResolutionFamilies
import Lax369799Proofs.FiniteCovers
import Lax369799.Renaming
import Lax369799Proofs.BoundedProfileRefinement

set_option backward.isDefEq.respectTransparency false
namespace Lax369799Proofs.FiniteResolutionNormalForms
open Lax369799.RankedSystems Lax369799.Morphisms Lax369799.Resolutions Lax369799.Renaming
open Lax369799.FiniteProfiles Lax369799.ResolutionFamilies Lax369799.FiniteResolutionNormalForms
open Lax369799.FinitePresentations (FiniteSystem)
open Lax369799Proofs.Pullbacks

private noncomputable abbrev roots {A : RankedSet} {n : ℕ} (S : SetSystem A n) :=
  { S.graph with initial := S.graph.root, root := ∅ }

private noncomputable def uprootMap {A : RankedSet} {n : ℕ} {S T : SetSystem A n}
    (f : Morphism S T) : Morphism (uproot S) (uproot T) :=
  trimMap ({
    toFun := f.toFun
    label := f.label
    initial := f.root
    root := fun _ h => False.elim h
    edge := f.edge } : Map (roots S) (roots T))

private theorem profile_mono {A B : RankedSet} (ρ : ∀ n, System A n → B n) {n : ℕ}
    {S T : SetSystem A n} (f : Morphism S T) (bound : ℕ) :
    BoundedProfile bound ρ S ⊆ BoundedProfile bound ρ T := by
  rintro e ⟨⟨R, ⟨r⟩, hr⟩, hb⟩
  exact ⟨⟨R, ⟨MorphismTheorems.compose r f⟩, hr⟩, hb⟩

private noncomputable def toSource {A : RankedSet} {n : ℕ} {S : SetSystem A n}
    (c : Component S) :
    { f : c.system.val.Vertex → S.Vertex //
      (∀ v, S.graph.label (f v) = c.system.val.graph.label v) ∧
      (∀ v, v ∈ c.system.val.graph.initial →
        (if c.rooted then S.graph.root else S.graph.initial) (f v)) ∧
      (∀ v d t, c.system.val.graph.edge v d t → S.graph.edge (f v) d (Sum.map f id t)) } := by
  classical
  cases hr : c.rooted with
  | false =>
    have h : DirectResolution S c.system := by simpa only [hr, Bool.false_eq_true, ↓reduceIte] using c.resolves
    let f := Classical.choice h
    refine ⟨f.toFun, f.label, ?_, f.edge⟩
    intro v hv
    simp only [Bool.false_eq_true, ↓reduceIte]
    exact f.initial v hv
  | true =>
    have h : DirectResolution (uproot S) c.system := by simpa only [hr, ↓reduceIte] using c.resolves
    let f := Classical.choice h
    refine ⟨fun v => vertex (roots S) (f.toFun v), f.label, ?_, ?_⟩
    · intro v hv
      simp only [↓reduceIte]
      exact f.initial v hv
    · intro v d t ht
      have h := f.edge v d t ht
      cases t <;> exact h

noncomputable def familyMap {A : RankedSet} {n : ℕ} {I : Type} [Fintype I]
    {S : SetSystem A n} (c : I → Component S) : Map (family c).graph S.graph := by
  classical
  let f : Map (familyGraph c) S.graph := {
    toFun := fun v => (toSource (c v.1)).val v.2
    label := fun v => (toSource (c v.1)).property.1 v.2
    initial := by
      rintro v ⟨hr, hv⟩
      simpa only [hr, Bool.false_eq_true, ↓reduceIte] using (toSource (c v.1)).property.2.1 v.2 hv
    root := by
      rintro v ⟨hr, hv⟩
      simpa only [hr, ↓reduceIte] using (toSource (c v.1)).property.2.1 v.2 hv
    edge := by
      rintro v d t ⟨s, hs, rfl⟩
      have h := (toSource (c v.1)).property.2.2 v.2 d s hs
      cases s <;> exact h }
  let e := Fintype.equivFin ((i : I) × (c i).system.val.Vertex)
  exact {
    toFun := fun v => f.toFun (e.symm v)
    label := fun _ => f.label _
    initial := fun _ h => f.initial _ h
    root := fun _ h => f.root _ h
    edge := by
      intro v d t ht
      have h := f.edge (e.symm v) d (Sum.map e.symm id t) ht
      cases t <;> exact h }

private noncomputable def injection {A : RankedSet} {n : ℕ} {I : Type} [Fintype I]
    {S : SetSystem A n} (c : I → Component S) (i : I) :
    {f : (c i).system.val.Vertex → (family c).Vertex //
      (∀ v, (family c).graph.label (f v) = (c i).system.val.graph.label v) ∧
      (∀ v, v ∈ (c i).system.val.graph.initial →
        (if (c i).rooted then (family c).graph.root else (family c).graph.initial) (f v)) ∧
      (∀ v d t, (c i).system.val.graph.edge v d t →
        (family c).graph.edge (f v) d (Sum.map f id t))} := by
  classical
  let e := Fintype.equivFin ((j : I) × (c j).system.val.Vertex)
  refine ⟨fun v => e ⟨i, v⟩, ?_, ?_, ?_⟩
  · intro v
    change (familyGraph c).label (e.symm (e ⟨i, v⟩)) = _
    simp only [Equiv.symm_apply_apply]
    rfl
  · intro v hv
    cases hr : (c i).rooted <;> simp only [Bool.false_eq_true, ↓reduceIte]
    · change (familyGraph c).initial (e.symm (e ⟨i, v⟩))
      simpa only [Equiv.symm_apply_apply] using (show (familyGraph c).initial ⟨i, v⟩ from ⟨hr, hv⟩)
    · change (familyGraph c).root (e.symm (e ⟨i, v⟩))
      simpa only [Equiv.symm_apply_apply] using (show (familyGraph c).root ⟨i, v⟩ from ⟨hr, hv⟩)
  · intro v d t ht
    change (familyGraph c).edge (e.symm (e ⟨i, v⟩)) d (Sum.map e.symm id (Sum.map (fun v => e ⟨i, v⟩) id t))
    rw [Equiv.symm_apply_apply]
    refine ⟨t, ht, ?_⟩
    cases t <;> simp

theorem injectionResolution {A : RankedSet} {n : ℕ} {I : Type} [Fintype I]
    {S : SetSystem A n} (c : I → Component S) (i : I) :
    DirectResolution (if (c i).rooted then uproot (trim (family c).graph) else trim (family c).graph)
      (c i).system := by
  classical
  let f := injection c i
  cases hr : (c i).rooted with
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    refine ⟨lift { toFun := f.val
                   label := f.property.1
                   initial := ?_
                   root := ?_
                   edge := f.property.2.2 }⟩
    · intro v hv
      have h := f.property.2.1 v hv
      simpa only [hr, Bool.false_eq_true, ↓reduceIte] using h
    · intro v hv
      rw [(c i).system.property.2.1] at hv
      exact False.elim hv
  | true =>
    simp only [↓reduceIte]
    let g : Map (plant (c i).system.val).graph (family c).graph := {
      toFun := f.val
      label := f.property.1
      initial := fun _ h => False.elim h
      root := by
        intro v hv
        rcases hv with hv | hv
        · rw [(c i).system.property.2.1] at hv
          exact False.elim hv
        · have h := f.property.2.1 v hv
          simpa only [hr, ↓reduceIte] using h
      edge := f.property.2.2 }
    let g' := lift g
    refine ⟨lift ({
      toFun := g'.toFun
      label := g'.label
      initial := fun v hv => g'.root v (Or.inr hv)
      root := ?_
      edge := g'.edge } : Map (c i).system.val.graph (roots (trim (family c).graph)))⟩
    intro v hv
    rw [(c i).system.property.2.1] at hv
    exact False.elim hv

private def initialComponent {A : RankedSet} {n : ℕ} {S : SetSystem A n}
    (w : Witness S) : Component S :=
  ⟨renameSystem w.variableMap w.system, false, w.resolves⟩

private def rootComponent {A : RankedSet} {n : ℕ} {S : SetSystem A n}
    (w : Witness (uproot S)) : Component S :=
  ⟨renameSystem w.variableMap w.system, true, w.resolves⟩

/--
---
conclusion: Lax369799.FiniteResolutionNormalForms.bounded_normal_form
---
Choose witnesses for all bounded initial and root entries. Their renamed
systems map into the original presentation, and each selected witness
maps into its own component of the finite disjoint family.
-/
theorem bounded_normal_form {A B : RankedSet} (hB : RankwiseFinite B) (bound : ℕ)
    (ρ : ∀ n, System A n → B n) {n : ℕ} (S : FiniteSystem A n) :
    ∃ (k : ℕ) (c : Fin k → Component (trim S.graph)),
      BoundedProfileEquivalent bound ρ S (family c) := by
  classical
  let S₀ := trim S.graph
  obtain ⟨k, w, _, hw⟩ := ResolutionFamilies.finite_family hB bound ρ S₀
  obtain ⟨l, u, _, hu⟩ := ResolutionFamilies.finite_family hB bound ρ (uproot S₀)
  let I := Fin k ⊕ Fin l
  let e := Fintype.equivFin I
  let c : Fin (Fintype.card I) → Component S₀ := fun j =>
    (e.symm j).elim (fun i => initialComponent (w i)) (fun i => rootComponent (u i))
  have hc (i : Fin k) : c (e (.inl i)) = initialComponent (w i) := by simp only [c, Equiv.symm_apply_apply, Sum.elim_inl]
  have hd (i : Fin l) : c (e (.inr i)) = rootComponent (u i) := by simp only [c, Equiv.symm_apply_apply, Sum.elim_inr]
  let f := project (familyMap c)
  refine ⟨Fintype.card I, c, ?_, ?_⟩
  · apply Set.Subset.antisymm
    · intro b hb
      obtain ⟨i, rfl⟩ := Set.mem_range.mp (hw ▸ hb)
      have hm := injectionResolution c (e (.inl i))
      rw [hc] at hm
      exact ⟨⟨(w i).system, hm, rfl⟩, (show (w i).entry ρ ∈ BoundedProfile bound ρ S₀ by rw [hw]; exact ⟨i, rfl⟩).2⟩
    · exact profile_mono ρ f bound
  · apply Set.Subset.antisymm
    · intro b hb
      obtain ⟨i, rfl⟩ := Set.mem_range.mp (hu ▸ hb)
      have hm := injectionResolution c (e (.inr i))
      rw [hd] at hm
      exact ⟨⟨(u i).system, hm, rfl⟩, (show (u i).entry ρ ∈ BoundedProfile bound ρ (uproot S₀) by rw [hu]; exact ⟨i, rfl⟩).2⟩
    · exact profile_mono ρ (uprootMap f) bound

/--
---
conclusion: Lax369799.FiniteResolutionNormalForms.contextual_normal_form
---
For a rankwise-finite unfolding-invariant recognizer, bounded profiles
refine contextual equivalence. The finite resolution family therefore
represents the original syntactic class.
-/
theorem contextual_normal_form {A B : RankedSet} (E : Lax369799.Algebras.Algebra B)
    (hE : Lax369799.Algebras.UnfoldInvariant E) (hB : RankwiseFinite B)
    (η : RankedMap A B) (F : Set (B 0)) (L : Lax369799.Algebras.Language A)
    (hL : Lax369799.Algebras.Recognizes E η F L) {n : ℕ} (S : FiniteSystem A n) :
    ∃ (k : ℕ) (c : Fin k → Component (trim S.graph)),
      Lax369799.FiniteContextualOrder.quotientMap (Lax369799.FiniteAcceptance.Accepting L) n S =
        Lax369799.FiniteContextualOrder.quotientMap (Lax369799.FiniteAcceptance.Accepting L) n (family c) := by
  let : Finite (B 1) := hB 1
  obtain ⟨k, c, hc⟩ := bounded_normal_form hB (Nat.card (B 1) + 1)
    (fun n R => E.eval n (relabelSystem η R)) S
  exact ⟨k, c, Quot.sound (BoundedProfileRefinement.refines E hE η F L hL S (family c) hc)⟩

end Lax369799Proofs.FiniteResolutionNormalForms
