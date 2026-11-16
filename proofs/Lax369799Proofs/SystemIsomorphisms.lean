import Lax369799.SystemIsomorphisms
import Lax369799Proofs.SupportPorts
import Lax369799Proofs.PresentationCovers

namespace Lax369799Proofs.SystemIsomorphisms
set_option backward.isDefEq.respectTransparency false
open Lax369799
open RankedSystems Morphisms FinitePresentations
open Lax369799Proofs.Pullbacks Lax369799Proofs.DeterministicNormalForms

private noncomputable def renamedOuter {A : RankedSet} {m n : ℕ}
    (σ : Fin m → Fin n) (S : RankedSystems.System A m) :
    RankedSystems.SetSystem (RankedSystems.SetSystem A) n :=
  RankedSystems.relabel (fun _ (U : RankedSystems.System A _) => U.val)
    (Renaming.renameSystem σ (RankedSystems.atomicSystem S)).val

private noncomputable def renameFlattenMap {A : RankedSet} {m n : ℕ}
    (σ : Fin m → Fin n) (S : RankedSystems.System A m) :
    Map (Lax369799Proofs.Flattening.graph (renamedOuter σ S))
      (Resolutions.rename σ S.val).graph where
  toFun := fun v => by exact v.2
  label := fun _ => rfl
  initial := by intro v h; exact h.2
  root := by
    intro v h
    rcases h with h | ⟨h, _⟩
    · exact h
    · exact False.elim h
  edge := by
    intro v d t ht
    rcases ht with ⟨w, hw, rfl⟩ | ⟨i, hi, ht⟩
    · exact ⟨.inl (by exact w), by exact hw, rfl⟩
    · rcases ht with ⟨w, hw, _, rfl⟩ | ⟨j, hj, rfl⟩
      · obtain ⟨u, ⟨a, he, rfl⟩, hu⟩ := hw
        cases hu
      · obtain ⟨u, ⟨a, he, rfl⟩, hu⟩ := hj
        have ha : (i : Fin m) = a := Fin.ext he
        subst a
        exact ⟨.inr (by exact i), by exact hi, by exact congrArg Sum.inr (Sum.inr.inj hu)⟩

private theorem renamed_reachable {A : RankedSet} {m n : ℕ}
    (σ : Fin m → Fin n) (S : RankedSystems.System A m)
    (v : (x : (renamedOuter σ S).Vertex) × (Lax369799.Flattening.Inner (renamedOuter σ S) x).Vertex) :
    (Lax369799Proofs.Flattening.graph (renamedOuter σ S)).Reachable v := by
  obtain ⟨r, hr, hp⟩ := S.val.reachable v.2
  have hi : r ∈ S.val.graph.initial := hr.elim id (fun h => by
    rw [S.property.2.1] at h; exact h.elim)
  refine ⟨⟨v.1,r⟩, Or.inl ⟨trivial,hi⟩, ?_⟩
  have liftPath : ∀ {a b : S.val.Vertex}, Relation.ReflTransGen S.val.graph.Step a b →
      Relation.ReflTransGen (Lax369799Proofs.Flattening.graph (renamedOuter σ S)).Step
        ⟨v.1,a⟩ ⟨v.1,b⟩ := by
    intro a b h
    induction h with
    | refl => exact .refl
    | @tail b c hp he ih =>
      obtain ⟨d,hd⟩ := he
      exact ih.tail ⟨d, Or.inl ⟨c,hd,rfl⟩⟩
  exact liftPath hp

private theorem renamed_bijective {A : RankedSet} {m n : ℕ}
    (σ : Fin m → Fin n) (S : RankedSystems.System A m) :
    Function.Bijective (project (renameFlattenMap σ S)).toFun := by
  classical
  let G := Lax369799Proofs.Flattening.graph (renamedOuter σ S)
  constructor
  · intro a b h
    apply (index G).symm.injective
    apply Subtype.ext
    apply Sigma.ext
    · apply Fin.ext
      change (vertex G a).1.val = (vertex G b).1.val
      have ha : (vertex G a).1.val < 1 := (vertex G a).1.isLt
      have hb : (vertex G b).1.val < 1 := (vertex G b).1.isLt
      omega
    · exact heq_of_eq h
  · intro w
    let v : (x : (renamedOuter σ S).Vertex) × (Lax369799.Flattening.Inner (renamedOuter σ S) x).Vertex :=
      ⟨⟨0,by change 0 < 1; omega⟩,w⟩
    refine ⟨index G ⟨v,renamed_reachable σ S v⟩, ?_⟩
    change (vertex G (index G _)).2 = w
    rw [vertex_index]

theorem renamed_iso {A : RankedSet} {m n : ℕ}
    (σ : Fin m → Fin n) (S : RankedSystems.System A m)
    (U : RankedSystems.System A n)
    (hU : Lax369799.Flattening.SystemFlattening (Renaming.renameSystem σ (RankedSystems.atomicSystem S)) U) :
    Isomorphic U.val (Renaming.renameSystem σ S).val := by
  change U.val = Flattening.flatten (renamedOuter σ S) at hU
  have hd : (Flattening.flatten (renamedOuter σ S)).Deterministic := hU ▸ U.property
  rw [hU]
  refine ⟨project (renameFlattenMap σ S), renamed_bijective σ S, ?_⟩
  exact MorphismTheorems.system_morphism_locally_surjective
    ⟨Flattening.flatten (renamedOuter σ S),hd⟩ _ _

private def morphismCover {A : RankedSet} {n : ℕ} {S T : SetSystem A n}
    (f : Morphism S T) (hf : f.LocallySurjective) : PresentationCovers.Cover S.graph T.graph where
  toFun := f.toFun
  initial := f.initial
  root := f.root
  label := f.label
  edge := f.edge
  initial_lift := hf.1
  root_lift := hf.2.1
  edge_lift := hf.2.2

/--
---
conclusion: Lax369799.SystemIsomorphisms.injective_isomorphic
---
-/
theorem injective_isomorphic {A : RankedSet} {n : ℕ} (S T : System A n)
    (f : Morphism S.val T.val) (hf : Function.Injective f.toFun) : Isomorphic S.val T.val := by
  have hc := MorphismTheorems.system_morphism_locally_surjective S T f
  exact ⟨f,⟨hf,PresentationCovers.surjective_of_reachable (morphismCover f hc) T.val.reachable⟩,hc⟩

/--
---
conclusion: Lax369799.SystemIsomorphisms.iso_symm
---
-/
theorem iso_symm {A : RankedSet} {n : ℕ} {S T : SetSystem A n}
    (h : Isomorphic S T) : Isomorphic T S := by
  classical
  obtain ⟨f,hf,hc⟩ := h
  let e : S.Vertex ≃ T.Vertex := Equiv.ofBijective f.toFun hf
  have hfg (v) : f.toFun (e.symm v) = v := e.apply_symm_apply v
  let g : Morphism T S := {
    toFun := e.symm
    initial := by
      intro w hw
      obtain ⟨v,hv,he⟩ := hc.1 w hw
      have hvw : e.symm w = v := by rw [← he]; exact e.symm_apply_apply v
      exact hvw.symm ▸ hv
    root := by
      intro w hw
      obtain ⟨v,hv,he⟩ := hc.2.1 w hw
      have hvw : e.symm w = v := by rw [← he]; exact e.symm_apply_apply v
      exact hvw.symm ▸ hv
    label := by intro w; exact ((hfg w) ▸ f.label (e.symm w)).symm
    edge := by
      intro w d t ht
      obtain ⟨u,hu,he⟩ := hc.2.2 (e.symm w) d t ((hfg w).symm ▸ ht)
      have hm : Sum.map e.symm id t = u := by
        rw [← he]
        cases u <;> simp [e]
      rw [hm]; exact hu }
  refine ⟨g,e.symm.bijective,?_,?_,?_⟩
  · intro v hv
    exact ⟨f.toFun v,f.initial v hv,e.symm_apply_apply v⟩
  · intro v hv
    exact ⟨f.toFun v,f.root v hv,e.symm_apply_apply v⟩
  · intro w d t ht
    refine ⟨Sum.map f.toFun id t, ?_, ?_⟩
    · have he := f.edge (e.symm w) d t ht
      rw [hfg] at he
      exact he
    · cases t <;> simp [g,e]

/--
---
conclusion: Lax369799.SystemIsomorphisms.iso_trans
---
-/
theorem iso_trans {A : RankedSet} {n : ℕ} {S T U : SetSystem A n}
    (hST : Isomorphic S T) (hTU : Isomorphic T U) : Isomorphic S U := by
  obtain ⟨f,hf,hfc⟩ := hST
  obtain ⟨g,hg,hgc⟩ := hTU
  obtain ⟨h,he,hc⟩ := MorphismTheorems.composition f g
  refine ⟨h,?_,hc hfc hgc⟩
  rw [he]
  exact hg.comp hf

theorem trimMap_injective {A : RankedSet} {n : ℕ} {V W : Type} [Fintype V] [Fintype W]
    {G : Presentation A n V} {H : Presentation A n W} (f : Map G H)
    (hf : Function.Injective f.toFun) : Function.Injective (trimMap f).toFun := by
  intro a b h
  apply vertex_injective G
  apply hf
  rw [← vertex_trimMap f a, ← vertex_trimMap f b,h]

/--
---
conclusion: Lax369799.SystemIsomorphisms.trim_isomorphic
---
-/
theorem trim_isomorphic {A : RankedSet} {n : ℕ} {V W : Type} [Fintype V] [Fintype W]
    {G : Presentation A n V} {H : Presentation A n W} (f : PresentationIso G H)
    (hG : (trim G).Deterministic) (hH : (trim H).Deterministic) :
    Isomorphic (trim G) (trim H) :=
  injective_isomorphic ⟨trim G,hG⟩ ⟨trim H,hH⟩ (trimMap (UntrimmedFlattening.isoMap f))
    (trimMap_injective _ f.vertex.injective)

private theorem embedding_injective {A : RankedSet} {n : ℕ} {V : Type} [Fintype V]
    (G : Presentation (System A) n V) : Function.Injective (flattenEmbedding G).toFun := by
  intro a b h
  obtain ⟨x,a⟩ := a
  obtain ⟨y,b⟩ := b
  have hxy : x = y := vertex_injective G (congrArg Sigma.fst h)
  subst y
  have hab : a = b := eq_of_heq (Sigma.mk.inj_iff.mp h).2
  subst b
  rfl

theorem flatten_trim_isomorphic {A : RankedSet} {n : ℕ} {V : Type} [Fintype V]
    (G : Presentation (System A) n V) (r : V) (hi : G.initial = {r}) (hr : G.root = ∅)
    (ht : ∀ v d, d < (G.label v).1 → ∃! t, G.edge v d t)
    (U : System A n)
    (hU : Flattening.SystemFlattening
      ⟨trim G,Yields.trim_deterministic G r hi hr ht⟩ U) :
    Isomorphic U.val (trim (rawFlatten G)) := by
  let R : System A n := ⟨trim (rawFlatten G),RawSystemFlattening.deterministic G r hi hr ht⟩
  change U.val = Flattening.flatten
    (RankedSystems.relabel (fun _ (S : System A _) => S.val) (trim G)) at hU
  have hd : (Flattening.flatten
    (RankedSystems.relabel (fun _ (S : System A _) => S.val) (trim G))).Deterministic :=
      hU ▸ U.property
  rw [hU]
  exact injective_isomorphic ⟨_,hd⟩ R (trimMap (flattenEmbedding G))
    (trimMap_injective _ (embedding_injective G))

def renameGraph {A : RankedSet} {m n : ℕ} {V : Type}
    (σ : Fin m → Fin n) (G : Presentation A m V) : Presentation A n V where
  label := G.label
  initial := G.initial
  root := G.root
  edge := fun v d t => ∃ u, G.edge v d u ∧ t = Sum.map id σ u
  direction_valid := by rintro v d t ⟨u,hu,_⟩; exact G.direction_valid v d u hu

theorem renameGraph_total {A : RankedSet} {m n : ℕ} {V : Type}
    (σ : Fin m → Fin n) (G : Presentation A m V)
    (ht : ∀ v d, d < (G.label v).1 → ∃! t, G.edge v d t) :
    ∀ v d, d < ((renameGraph σ G).label v).1 → ∃! t, (renameGraph σ G).edge v d t := by
  intro v d hd
  obtain ⟨t,ht,hu⟩ := ht v d hd
  refine ⟨Sum.map id σ t,⟨t,ht,rfl⟩,?_⟩
  rintro u ⟨t',ht',rfl⟩
  exact congrArg (Sum.map id σ) (hu t' ht')

private noncomputable def renameTrimMap {A : RankedSet} {m n : ℕ} {V : Type} [Fintype V]
    (σ : Fin m → Fin n) (G : Presentation A m V) :
    Map (Resolutions.rename σ (trim G)).graph (renameGraph σ G) where
  toFun := vertex G
  label := fun _ => rfl
  initial := fun _ h => h
  root := fun _ h => h
  edge := by
    rintro v d t ⟨u,hu,rfl⟩
    refine ⟨Sum.map (vertex G) id u,hu,?_⟩
    cases u <;> rfl

private theorem lift_injective {A : RankedSet} {n : ℕ} {V : Type} [Fintype V]
    {S : SetSystem A n} {G : Presentation A n V} (f : Map S.graph G)
    (hf : Function.Injective f.toFun) : Function.Injective (lift f).toFun := by
  intro a b h
  apply hf
  have hv (v) : vertex G ((lift f).toFun v) = f.toFun v := vertex_index G _ _
  rw [← hv a,← hv b,h]

theorem raw_total {A : RankedSet} {n : ℕ} {V : Type}
    (G : Presentation (System A) n V)
    (total : ∀ v d, d < (G.label v).1 → ∃! t, G.edge v d t) :
    ∀ v d, d < ((rawFlatten G).label v).1 → ∃! t, (rawFlatten G).edge v d t := by
  classical
  let H := rawFlatten G
  let initial (v : V) := Classical.choose (G.label v).2.property.1
  have initial_spec (v : V) :
      (G.label v).2.val.graph.initial = {initial v} :=
    Classical.choose_spec (G.label v).2.property.1
  let outer (v : V) (i : Fin (G.label v).1) :=
    Classical.choose (total v i.val i.isLt)
  have outer_edge (v : V) (i : Fin (G.label v).1) :
      G.edge v i.val (outer v i) :=
    (Classical.choose_spec (total v i.val i.isLt)).1
  have outer_unique (v : V) (i : Fin (G.label v).1)
      (t : V ⊕ Fin n) (ht : G.edge v i.val t) : t = outer v i :=
    (Classical.choose_spec (total v i.val i.isLt)).2 t ht
  let next (v : V) (t : (G.label v).2.val.Vertex ⊕ Fin (G.label v).1) :
      ((v : V) × (G.label v).2.val.Vertex) ⊕ Fin n :=
    match t with
    | .inl w => .inl ⟨v, w⟩
    | .inr i => match outer v i with
      | .inl w => .inl ⟨w, initial w⟩
      | .inr j => .inr j
  have edge_iff (v : (v : V) × (G.label v).2.val.Vertex) (d : ℕ) (t) :
      H.edge v d t ↔ ∃ s, (G.label v.1).2.val.graph.edge v.2 d s ∧ t = next v.1 s := by
    constructor
    · rintro (⟨w, hw, rfl⟩ | ⟨i, hi, h⟩)
      · exact ⟨.inl w, hw, rfl⟩
      · refine ⟨.inr i, hi, ?_⟩
        rcases h with ⟨w, hw, hw', rfl⟩ | ⟨j, hj, rfl⟩
        · have he := outer_unique v.1 i (.inl w.1) hw
          have hin : w.2 = initial w.1 := by
            have h : (G.label w.1).2.val.graph.initial w.2 := hw'
            rw [initial_spec w.1] at h
            exact h
          simp only [next, ← he]
          exact congrArg Sum.inl (Sigma.ext rfl (heq_of_eq hin))
        · have he := outer_unique v.1 i (.inr j) hj
          simp only [next, ← he]
    · rintro ⟨s, hs, rfl⟩
      cases s with
      | inl w => exact Or.inl ⟨w, hs, rfl⟩
      | inr i =>
        refine Or.inr ⟨i, hs, ?_⟩
        cases ho : outer v.1 i with
        | inl w =>
          refine Or.inl ⟨⟨w, initial w⟩, ?_, ?_, ?_⟩
          · have h := outer_edge v.1 i
            rw [ho] at h; exact h
          · change (G.label w).2.val.graph.initial (initial w)
            rw [initial_spec]; rfl
          · simp only [next, ho]
        | inr j =>
          refine Or.inr ⟨j, ?_, ?_⟩
          · have h := outer_edge v.1 i
            rw [ho] at h; exact h
          · simp only [next, ho]
  intro v d hd
  obtain ⟨s, hs, hu⟩ := (G.label v.1).2.property.2.2 v.2 d hd
  refine ⟨next v.1 s, (edge_iff v d _).mpr ⟨s, hs, rfl⟩, ?_⟩
  intro t ht
  obtain ⟨u, hu', he⟩ := (edge_iff v d t).mp ht
  rw [hu u hu'] at he
  exact he

theorem rename_trim_isomorphic {A : RankedSet} {m n : ℕ} {V : Type} [Fintype V]
    (σ : Fin m → Fin n) (G : Presentation A m V) (r : V)
    (hi : G.initial = {r}) (hr : G.root = ∅)
    (ht : ∀ v d, d < (G.label v).1 → ∃! t, G.edge v d t) :
    Isomorphic (Resolutions.rename σ (trim G)) (trim (renameGraph σ G)) := by
  let R : System A m := ⟨trim G,Yields.trim_deterministic G r hi hr ht⟩
  let T : System A n := ⟨trim (renameGraph σ G),Yields.trim_deterministic
    (renameGraph σ G) r hi hr (renameGraph_total σ G ht)⟩
  exact injective_isomorphic (Renaming.renameSystem σ R) T (lift (renameTrimMap σ G))
    (lift_injective _ (vertex_injective G))

private theorem rename_internal {A : RankedSet} {m n : ℕ} {V : Type}
    (σ : Fin m → Fin n) (G : Presentation A m V) (v w : V) (d : ℕ) :
    (renameGraph σ G).edge v d (.inl w) ↔ G.edge v d (.inl w) := by
  constructor
  · rintro ⟨t,ht,he⟩
    cases t with
    | inl u => cases he; exact ht
    | inr i => cases he
  · intro h; exact ⟨.inl w,h,rfl⟩

private theorem rename_variable {A : RankedSet} {m n : ℕ} {V : Type}
    (σ : Fin m → Fin n) (G : Presentation A m V) (v : V) (d : ℕ) (j : Fin n) :
    (renameGraph σ G).edge v d (.inr j) ↔ ∃ i, G.edge v d (.inr i) ∧ j = σ i := by
  constructor
  · rintro ⟨t,ht,he⟩
    cases t with
    | inl u => cases he
    | inr i => exact ⟨i,ht,Sum.inr.inj he⟩
  · rintro ⟨i,hi,rfl⟩; exact ⟨.inr i,hi,rfl⟩

private theorem flatten_internal {A : RankedSet} {n : ℕ} {V : Type}
    (G : Presentation (System A) n V) (v w : (x : V) × (G.label x).2.val.Vertex) (d : ℕ) :
    (rawFlatten G).edge v d (.inl w) ↔
      (∃ z, (G.label v.1).2.val.graph.edge v.2 d (.inl z) ∧ w = ⟨v.1,z⟩) ∨
      (∃ i, (G.label v.1).2.val.graph.edge v.2 d (.inr i) ∧
        G.edge v.1 i.val (.inl w.1) ∧ (G.label w.1).2.val.graph.initial w.2) := by
  constructor
  · rintro (⟨z,hz,he⟩ | ⟨i,hi,h⟩)
    · exact Or.inl ⟨z,hz,Sum.inl.inj he⟩
    · rcases h with ⟨u,hu,hm,he⟩ | ⟨j,hj,he⟩
      · have hwu : w = u := Sum.inl.inj he
        subst u
        exact Or.inr ⟨i,hi,hu,hm⟩
      · cases he
  · rintro (⟨z,hz,he⟩ | ⟨i,hi,he,hm⟩)
    · exact Or.inl ⟨z,hz,congrArg Sum.inl he⟩
    · exact Or.inr ⟨i,hi,Or.inl ⟨w,he,hm,rfl⟩⟩

private theorem flatten_variable {A : RankedSet} {n : ℕ} {V : Type}
    (G : Presentation (System A) n V) (v : (x : V) × (G.label x).2.val.Vertex)
    (d : ℕ) (j : Fin n) :
    (rawFlatten G).edge v d (.inr j) ↔
      ∃ i, (G.label v.1).2.val.graph.edge v.2 d (.inr i) ∧ G.edge v.1 i.val (.inr j) := by
  constructor
  · rintro (⟨z,hz,he⟩ | ⟨i,hi,h⟩)
    · cases he
    · rcases h with ⟨u,hu,hm,he⟩ | ⟨k,hk,he⟩
      · cases he
      · have hjk : j = k := Sum.inr.inj he
        subst k
        exact ⟨i,hi,hk⟩
  · rintro ⟨i,hi,he⟩
    exact Or.inr ⟨i,hi,Or.inr ⟨j,he,rfl⟩⟩

def flatten_rename_iso {A : RankedSet} {m n : ℕ} {V : Type}
    (σ : Fin m → Fin n) (G : Presentation (System A) m V) :
    PresentationIso (rawFlatten (renameGraph σ G)) (renameGraph σ (rawFlatten G)) where
  vertex := Equiv.refl _
  label := fun _ => rfl
  initial := fun _ => Iff.rfl
  root := fun _ => Iff.rfl
  edge := by
    intro v d t
    cases t with
    | inl w =>
      change (renameGraph σ (rawFlatten G)).edge v d (.inl w) ↔
        (rawFlatten (renameGraph σ G)).edge v d (.inl w)
      rw [rename_internal σ (rawFlatten G),flatten_internal G,flatten_internal (renameGraph σ G)]
      simp only [rename_internal]
      rfl
    | inr j =>
      change (renameGraph σ (rawFlatten G)).edge v d (.inr j) ↔
        (rawFlatten (renameGraph σ G)).edge v d (.inr j)
      rw [rename_variable σ (rawFlatten G),flatten_variable (renameGraph σ G)]
      simp_rw [flatten_variable G,rename_variable σ G]
      constructor
      · rintro ⟨i,⟨k,hk,he⟩,hji⟩
        exact ⟨k,hk,i,he,hji⟩
      · rintro ⟨k,hk,i,he,hji⟩
        exact ⟨i,⟨k,hk,he⟩,hji⟩

theorem raw_marks {A : RankedSet} {n : ℕ} {V : Type}
    (G : Presentation (System A) n V) (r : V)
    (hi : G.initial = {r}) (hr : G.root = ∅) :
    (∃ z, (rawFlatten G).initial = {z}) ∧ (rawFlatten G).root = ∅ := by
  classical
  let i := Classical.choose (G.label r).2.property.1
  have him : (G.label r).2.val.graph.initial = {i} := Classical.choose_spec (G.label r).2.property.1
  constructor
  · refine ⟨⟨r,i⟩,?_⟩
    ext v
    change (G.initial v.1 ∧ (G.label v.1).2.val.graph.initial v.2) ↔ v = ⟨r,i⟩
    rw [hi]
    constructor
    · rintro ⟨hv,hw⟩
      have hv : v.1 = r := hv
      obtain ⟨v,w⟩ := v
      dsimp at hv
      subst v
      rw [him] at hw
      have hw : w = i := hw
      subst w
      rfl
    · rintro rfl
      exact ⟨rfl,by rw [him];rfl⟩
  · ext v
    change ((G.label v.1).2.val.graph.root v.2 ∨
      (G.root v.1 ∧ (G.label v.1).2.val.graph.initial v.2)) ↔ False
    rw [(G.label v.1).2.property.2.1,hr]
    exact ⟨fun h => h.elim id And.left,False.elim⟩

/--
---
conclusion: Lax369799.SystemIsomorphisms.flatten_output_rename
---
-/
theorem flatten_output_rename {A : RankedSet} {m n : ℕ} (σ : Fin m → Fin n)
    (P : System (System A) m) (U : System A m) (W : System A n)
    (hU : Flattening.SystemFlattening P U)
    (hW : Flattening.SystemFlattening (Renaming.renameSystem σ P) W) :
    Isomorphic (Renaming.renameSystem σ U).val W.val := by
  classical
  let G := P.val.graph
  obtain ⟨r,hr⟩ := P.property.1
  obtain ⟨⟨z,hz⟩,hroots⟩ := raw_marks G r hr P.property.2.1
  have ht := raw_total G P.property.2.2
  have hren := rename_trim_isomorphic σ (rawFlatten G) z hz hroots ht
  have hd : (trim (rawFlatten G)).Deterministic :=
    RawSystemFlattening.deterministic G r hr P.property.2.1 P.property.2.2
  have hdr : (trim (renameGraph σ (rawFlatten G))).Deterministic :=
    Yields.trim_deterministic _ z hz hroots (renameGraph_total σ _ ht)
  have hdw : (trim (rawFlatten (renameGraph σ G))).Deterministic := by
    change W.val = trim (rawFlatten (renameGraph σ G)) at hW
    exact hW ▸ W.property
  have hiso := trim_isomorphic (flatten_rename_iso σ G) hdw hdr
  have hres := iso_trans hren (iso_symm hiso)
  change U.val = trim (rawFlatten G) at hU
  change W.val = trim (rawFlatten (renameGraph σ G)) at hW
  change Isomorphic (Resolutions.rename σ U.val) W.val
  rw [hU,hW]
  exact hres

/--
---
conclusion: Lax369799.SystemIsomorphisms.flatten_from_trim
---
-/
theorem flatten_from_trim {A : RankedSet} {n : ℕ} {V : Type} [Fintype V]
    (G : Presentation (System A) n V) (r : V) (hi : G.initial = {r}) (hr : G.root = ∅)
    (ht : ∀ v d, d < (G.label v).1 → ∃! t, G.edge v d t)
    (P : System (System A) n) (hP : P.val = trim G)
    (U : System A n) (hU : Flattening.SystemFlattening P U) :
    Isomorphic U.val (trim (SupportPorts.flattened G)) := by
  have hp : P = ⟨trim G,Yields.trim_deterministic G r hi hr ht⟩ := Subtype.ext hP
  rw [hp] at hU
  exact flatten_trim_isomorphic G r hi hr ht U hU

end Lax369799Proofs.SystemIsomorphisms
