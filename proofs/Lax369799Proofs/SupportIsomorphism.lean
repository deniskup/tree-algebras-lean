import Lax369799.SupportIsomorphism
import Lax369799Proofs.SupportEvaluation

namespace Lax369799Proofs.SupportIsomorphism
set_option backward.isDefEq.respectTransparency false
open Lax369799
open RankedSystems Morphisms Renaming
open SupportedSystems (FullySupported)

private theorem sum_inj {V : Type} {m n : ℕ} (σ : Fin m → Fin n)
    (hσ : Function.Injective σ) : Function.Injective (Sum.map (id : V → V) σ) := by
  intro x y h
  cases x <;> cases y <;> simp only [Sum.map_inl,Sum.map_inr,id_eq,Sum.inl.injEq,
    Sum.inr.injEq,reduceCtorEq] at h ⊢
  · exact h
  · exact hσ h

private theorem graph_ext {A : RankedSet} {n : ℕ} {V : Type}
    (G H : Presentation A n V) (hl : G.label = H.label) (hi : G.initial = H.initial)
    (hr : G.root = H.root) (he : G.edge = H.edge) : G = H := by
  cases G; cases H; cases hl; cases hi; cases hr; cases he; rfl

private theorem system_ext {A : RankedSet} {n : ℕ} (S T : SetSystem A n)
    (hs : S.size = T.size) (hg : HEq S.graph T.graph) : S = T := by
  cases S; cases T; cases hs; cases hg; rfl

/--
---
conclusion: Lax369799.SupportIsomorphism.compact_along
---
-/
theorem compact_along {A : RankedSet} {m n : ℕ} (S : System A n)
    (σ : Fin m → Fin n) (hσ : Function.Injective σ)
    (hs : ∀ j, (∃ v d, S.val.graph.edge v d (.inr j)) ↔ j ∈ Set.range σ) :
    ∃ T : SupportedSystems.System A m, renameSystem σ T.val = S := by
  classical
  let G : Presentation A m S.val.Vertex := {
    label := S.val.graph.label
    initial := S.val.graph.initial
    root := S.val.graph.root
    edge := fun v d t => S.val.graph.edge v d (Sum.map id σ t)
    direction_valid := fun v d t h => S.val.graph.direction_valid v d _ h }
  have hreach : ∀ v, G.Reachable v := by
    intro v
    obtain ⟨r,hr,hp⟩ := S.val.reachable v
    exact ⟨r,hr,Relation.ReflTransGen.mono (fun _ _ ⟨d,hd⟩ => ⟨d,hd⟩) _ _ hp⟩
  have hpre : ∀ v d t, S.val.graph.edge v d t →
      ∃ u, G.edge v d u ∧ Sum.map id σ u = t := by
    intro v d t ht
    cases t with
    | inl w => exact ⟨.inl w,ht,rfl⟩
    | inr j =>
      obtain ⟨i,hi⟩ := (hs j).mp ⟨v,d,ht⟩
      refine ⟨.inr i, ?_, congrArg Sum.inr hi⟩
      change S.val.graph.edge v d (.inr (σ i))
      rw [hi]; exact ht
  let U : System A m := ⟨⟨S.val.size,G,hreach⟩, S.property.1,S.property.2.1,by
    intro v d hd
    obtain ⟨t,ht,hu⟩ := S.property.2.2 v d hd
    obtain ⟨u,he,hm⟩ := hpre v d t ht
    refine ⟨u,he,fun u' hu' => sum_inj σ hσ ((hu _ hu').trans hm.symm)⟩⟩
  have hsupport : FullySupported U := by
    intro i
    obtain ⟨v,d,hd⟩ := (hs (σ i)).mpr (Set.mem_range_self i)
    exact ⟨v,d,hd⟩
  refine ⟨⟨U,hsupport⟩, ?_⟩
  apply Subtype.ext
  have he : (renameSystem σ U).val.graph.edge = S.val.graph.edge := by
    funext v d t
    apply propext
    constructor
    · rintro ⟨u,hu,rfl⟩; exact hu
    · intro ht
      obtain ⟨u,hu,he⟩ := hpre v d t ht
      exact ⟨u,hu,he.symm⟩
  exact system_ext _ _ rfl (heq_of_eq (graph_ext _ _ rfl rfl rfl he))

/--
---
conclusion: Lax369799.SupportIsomorphism.reflect_morphism
---
-/
theorem reflect_morphism {A : RankedSet} {m n : ℕ} (σ : Fin m → Fin n)
    (hσ : Function.Injective σ) (S T : System A m)
    (f : Morphism (renameSystem σ S).val (renameSystem σ T).val) :
    ∃ g : Morphism S.val T.val, g.toFun = f.toFun := by
  refine ⟨{
    toFun := f.toFun
    initial := f.initial
    root := f.root
    label := f.label
    edge := ?_ },rfl⟩
  intro v d t ht
  have he := f.edge v d (Sum.map id σ t) ⟨t,ht,rfl⟩
  obtain ⟨u,hu,he⟩ := he
  have hm : Sum.map id σ (Sum.map f.toFun id t) = Sum.map id σ u := by
    cases t <;> exact he
  exact sum_inj σ hσ hm ▸ hu

/--
---
conclusion: Lax369799.SupportIsomorphism.occurs_isomorphic
---
-/
theorem occurs_isomorphic {A : RankedSet} {n : ℕ} (S T : System A n)
    (h : Isomorphic S.val T.val) (j : Fin n) :
    (∃ v d, S.val.graph.edge v d (.inr j)) ↔ ∃ v d, T.val.graph.edge v d (.inr j) := by
  obtain ⟨f,hf,hc⟩ := h
  constructor
  · rintro ⟨v,d,hd⟩
    exact ⟨f.toFun v,d,f.edge v d (.inr j) hd⟩
  · rintro ⟨w,d,hd⟩
    obtain ⟨v,rfl⟩ := hf.2 w
    obtain ⟨t,ht,he⟩ := hc.2.2 v d (.inr j) hd
    cases t with
    | inl u => cases he
    | inr i => cases he; exact ⟨v,d,ht⟩

/--
---
conclusion: Lax369799.SupportIsomorphism.profile_isomorphic
---
-/
theorem profile_isomorphic {B : RankedSet} (E : SupportedAlgebras.Algebra B) {n : ℕ}
    (S T : System B n) (h : Isomorphic S.val T.val) :
    SupportEvaluation.Equivalent E S T := by
  obtain ⟨o,U,hU,heU⟩ := SupportEvaluation.profile_nonempty E S
  have hsupport : ∀ j, (∃ v d, T.val.graph.edge v d (.inr j)) ↔ j ∈ Set.range o.ports := by
    intro j
    rw [← occurs_isomorphic S T h j, ← hU]
    exact SupportCompaction.support_image o.ports U j
  obtain ⟨W,hW⟩ := compact_along T o.ports o.ports.injective hsupport
  have hIso : Isomorphic (renameSystem o.ports U.val).val (renameSystem o.ports W.val).val := by
    rw [hU,hW]; exact h
  obtain ⟨f,hf,_⟩ := hIso
  obtain ⟨g,hg⟩ := reflect_morphism o.ports o.ports.injective U.val W.val f
  have hUW : Isomorphic U.val.val W.val.val :=
    ⟨g,hg ▸ hf,MorphismTheorems.system_morphism_locally_surjective U.val W.val g⟩
  apply (SupportEvaluation.equivalent_iff E S T).mpr
  exact ⟨o.arity.val,o.ports,o.ports.injective,U,W,hU,hW,E.isomorphic _ U W hUW⟩

/--
---
conclusion: Lax369799.SupportIsomorphism.profile_injective_rename
---
-/
theorem profile_injective_rename {B : RankedSet} (E : SupportedAlgebras.Algebra B)
    {m n : ℕ} (σ : Fin m → Fin n) (hσ : Function.Injective σ)
    (S T : System B m) (h : SupportEvaluation.Equivalent E S T) :
    SupportEvaluation.Equivalent E (renameSystem σ S) (renameSystem σ T) := by
  obtain ⟨k,τ,hτ,U,W,hU,hW,he⟩ := (SupportEvaluation.equivalent_iff E S T).mp h
  apply (SupportEvaluation.equivalent_iff E _ _).mpr
  refine ⟨k,σ ∘ τ,hσ.comp hτ,U,W,?_,?_,he⟩
  · rw [← hU]
    apply Subtype.ext
    exact (Renaming.rename_composition τ σ U.val.val).symm
  · rw [← hW]
    apply Subtype.ext
    exact (Renaming.rename_composition τ σ W.val.val).symm

end Lax369799Proofs.SupportIsomorphism
