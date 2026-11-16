import Lax369799.ContextPorts
import Lax369799Proofs.SupportedCompletionProperties
import Lax369799Proofs.ContinuationCompression
import Lax369799Proofs.SupportPorts

set_option backward.isDefEq.respectTransparency false
namespace Lax369799Proofs.ContextPorts
open scoped Classical
open Lax369799
open RankedSystems Flattening
open Lax369799.ContextPorts (resizeSymbol resizeGraph)

private theorem symbol_hole {A : RankedSet} {m : ℕ} (k : ℕ) (a : Symbol (WithHole A m)) :
    IsHole (resizeSymbol k a) ↔ IsHole a := by
  obtain ⟨r,a⟩ := a
  cases a <;> simp [resizeSymbol,IsHole]

private theorem symbol_rank {A : RankedSet} {m : ℕ} (k : ℕ) (a : Symbol (WithHole A m))
    (h : ¬IsHole a) : (resizeSymbol k a).1 = a.1 := by
  obtain ⟨r,a⟩ := a
  cases a with
  | inl a => rfl
  | inr e => exact (h ⟨e,rfl⟩).elim

private theorem old_hole_rank {A : RankedSet} {m : ℕ} (a : Symbol (WithHole A m))
    (h : IsHole a) : a.1 = m := by
  obtain ⟨r,a⟩ := a
  cases a with
  | inl a => obtain ⟨e,he⟩ := h; cases he
  | inr e => exact e.down.symm

private theorem new_hole_rank {A : RankedSet} {m : ℕ} (k : ℕ) (a : Symbol (WithHole A m))
    (h : IsHole a) : (resizeSymbol k a).1 = k := by
  obtain ⟨r,a⟩ := a
  cases a with
  | inl a => obtain ⟨e,he⟩ := h; cases he
  | inr e => rfl

private noncomputable def hole {A : RankedSet} {m : ℕ} (C : SetContext A m 0) : C.system.Vertex :=
  Classical.choose C.one_hole

private theorem hole_spec {A : RankedSet} {m : ℕ} (C : SetContext A m 0) :
    IsHole (C.system.graph.label (hole C)) ∧
      ∀ v, IsHole (C.system.graph.label v) → v = hole C := Classical.choose_spec C.one_hole

private theorem hole_reachable {A : RankedSet} {m k : ℕ} (C : SetContext A m 0) (s : Fin k → Fin m) :
    (resizeGraph C s).Reachable (hole C) := by
  classical
  obtain ⟨r,hr,hp⟩ := C.system.reachable (hole C)
  have lift {v : C.system.Vertex} (p : Relation.ReflTransGen C.system.graph.Step r v) :
      (resizeGraph C s).Reachable v ∨ (resizeGraph C s).Reachable (hole C) := by
    induction p with
    | refl => exact Or.inl ⟨r,hr,.refl⟩
    | @tail v w hp hstep ih =>
      rcases ih with hv | hh
      · by_cases he : v = hole C
        · exact Or.inr (he ▸ hv)
        · have hn : ¬IsHole (C.system.graph.label v) := fun h => he ((hole_spec C).2 v h)
          obtain ⟨d,hd⟩ := hstep
          obtain ⟨a,ha,hpath⟩ := hv
          exact Or.inl ⟨a,ha,hpath.tail ⟨d,by simpa only [resizeGraph,if_neg hn] using hd⟩⟩
      · exact Or.inr hh
  exact (lift hp).elim id id

noncomputable def resizeContext {A : RankedSet} {m k : ℕ} (C : SetContext A m 0)
    (s : Fin k → Fin m) : SetContext A k 0 := by
  classical
  let G := resizeGraph C s
  refine ⟨trim G,?_⟩
  refine ⟨Pullbacks.index G ⟨hole C,hole_reachable C s⟩,?_,?_⟩
  · change IsHole (G.label (Pullbacks.vertex G (Pullbacks.index G _)))
    rw [Pullbacks.vertex_index]
    exact (symbol_hole k _).mpr (hole_spec C).1
  · intro v hv
    apply Pullbacks.vertex_injective G
    rw [Pullbacks.vertex_index]
    exact (hole_spec C).2 _ ((symbol_hole k _).mp hv)

theorem resize_deterministic {A : RankedSet} {m k : ℕ} (C : SetContext A m 0)
    (hC : C.system.Deterministic) (s : Fin k → Fin m) : (resizeContext C s).system.Deterministic := by
  classical
  obtain ⟨i,hi⟩ := hC.1
  apply Yields.trim_deterministic (resizeGraph C s) i hi hC.2.1
  intro v d hd
  by_cases h : IsHole (C.system.graph.label v)
  · have hk : d < k := by simpa only [resizeGraph,new_hole_rank k _ h] using hd
    let j : Fin k := ⟨d,hk⟩
    have hs : (s j).val < (C.system.graph.label v).1 := by
      rw [old_hole_rank _ h]; exact (s j).isLt
    obtain ⟨t,ht,hu⟩ := hC.2.2 v (s j).val hs
    refine ⟨t,?_,?_⟩
    · change (if IsHole (C.system.graph.label v) then _ else _)
      rw [if_pos h]
      exact ⟨j,rfl,ht⟩
    · intro u hu'
      change (if IsHole (C.system.graph.label v) then _ else _) at hu'
      rw [if_pos h] at hu'
      obtain ⟨a,ha,ha'⟩ := hu'
      have he : a = j := Fin.ext ha.symm
      subst a
      exact hu u ha'
  · have ho : d < (C.system.graph.label v).1 := by simpa only [resizeGraph,symbol_rank k _ h] using hd
    obtain ⟨t,ht,hu⟩ := hC.2.2 v d ho
    refine ⟨t,?_,?_⟩
    · simpa only [resizeGraph,if_neg h] using ht
    · intro u hu'
      exact hu u (by simpa only [resizeGraph,if_neg h] using hu')


private theorem trim_iso {A : RankedSet} {n : ℕ} {V W : Type} [Fintype V] [Fintype W]
    {G : Presentation A n V} {H : Presentation A n W} (f : FinitePresentations.PresentationIso G H) :
    Morphisms.Isomorphic (trim G) (trim H) := by
  let m := UntrimmedFlattening.isoMap f
  let c := FiniteCovers.isoCover f
  let g := Pullbacks.trimMap m
  have hc := Pullbacks.trimMap_surjective m c.initial_lift c.root_lift c.edge_lift
  let cg : PresentationCovers.Cover (trim G).graph (trim H).graph :=
    ⟨g.toFun,g.label,g.initial,g.root,g.edge,hc.1,hc.2.1,hc.2.2⟩
  exact ⟨g,⟨SystemIsomorphisms.trimMap_injective m f.vertex.injective,
    PresentationCovers.surjective_of_reachable cg (trim H).reachable⟩,hc⟩

private def arity {A : RankedSet} {m : ℕ} (k : ℕ) : Symbol (WithHole A m) → ℕ
  | ⟨r,.inl _⟩ => r
  | ⟨_,.inr _⟩ => k

private def ports {A : RankedSet} {m k : ℕ} (s : Fin k → Fin m) :
    (a : Symbol (WithHole A m)) → Fin (arity k a) → Fin a.1
  | ⟨_,.inl _⟩ => id
  | ⟨_,.inr ⟨h⟩⟩ => fun i => Fin.cast h (s i)

private def inner {A : RankedSet} {m k : ℕ} (R : System A k) :
    (a : Symbol (WithHole A m)) → System A (arity k a)
  | ⟨_,.inl a⟩ => atomicSystem a
  | ⟨_,.inr _⟩ => R

private theorem rename_id {A : RankedSet} {m : ℕ} (S : System A m) :
    Renaming.renameSystem id S = S := Subtype.ext (Renaming.rename_identity S.val)

private theorem expanded_label {A : RankedSet} {m k : ℕ} (s : Fin k → Fin m) (R : System A k)
    (a : Symbol (WithHole A m)) :
    (⟨a.1,Renaming.renameSystem (ports s a) (inner R a)⟩ : Symbol (System A)) =
      ⟨a.1,SystemEvaluation.substituteSystem (Renaming.renameSystem s R) a.1 a.2⟩ := by
  obtain ⟨r,a⟩ := a
  cases a with
  | inl a => change Sigma.mk r (Renaming.renameSystem id (atomicSystem a)) = _; rw [rename_id]; rfl
  | inr e => obtain ⟨h⟩ := e; subst r; rfl

private theorem restricted_label {A : RankedSet} {m k : ℕ} (R : System A k) (a : Symbol (WithHole A m)) :
    (⟨arity k a,inner R a⟩ : Symbol (System A)) =
      ⟨(resizeSymbol k a).1,SystemEvaluation.substituteSystem R (resizeSymbol k a).1 (resizeSymbol k a).2⟩ := by
  obtain ⟨r,a⟩ := a
  cases a <;> rfl

private def substituteGraph {A : RankedSet} {m n : ℕ} {V : Type}
    (G : Presentation (WithHole A m) n V) (R : System A m) : Presentation (System A) n V := {
  G with label := fun v => ⟨(G.label v).1,SystemEvaluation.substituteSystem R _ (G.label v).2⟩ }

private theorem restrict_edges {A : RankedSet} {m k : ℕ} {T : Type}
    (s : Fin k → Fin m) (a : Symbol (WithHole A m)) (E : ℕ → T → Prop)
    (hE : ∀ d t,E d t → d < a.1) (d : ℕ) (t : T) :
    (if IsHole a then ∃ i : Fin k,d = i.val ∧ E (s i).val t else E d t) ↔
      ∃ i : Fin (arity k a),d = i.val ∧ E (ports s a i).val t := by
  classical
  obtain ⟨r,a⟩ := a
  cases a with
  | inl a =>
    have hn : ¬IsHole (⟨r,Sum.inl a⟩ : Symbol (WithHole A m)) := by rintro ⟨e,he⟩; cases he
    rw [if_neg hn]
    change E d t ↔ ∃ i : Fin r,d = i.val ∧ E i.val t
    constructor
    · intro ht; exact ⟨⟨d,hE d t ht⟩,rfl,ht⟩
    · rintro ⟨i,rfl,ht⟩; exact ht
  | inr e =>
    have hh : IsHole (⟨r,Sum.inr e⟩ : Symbol (WithHole A m)) := ⟨e,rfl⟩
    rw [if_pos hh]
    obtain ⟨h⟩ := e; subst r; rfl

private def restricted_iso {A : RankedSet} {m k : ℕ} (C : SetContext A m 0)
    (s : Fin k → Fin m) (R : System A k) :
    FinitePresentations.PresentationIso
      (SupportPorts.restricted C.system.graph (fun v => arity k (C.system.graph.label v))
        (fun v => ports s (C.system.graph.label v)) (fun v => inner R (C.system.graph.label v)))
      (substituteGraph (resizeGraph C s) R) where
  vertex := Equiv.refl _
  label := fun v => (restricted_label R (C.system.graph.label v)).symm
  initial := fun _ => Iff.rfl
  root := fun _ => Iff.rfl
  edge := by
    intro v d t
    cases t with
    | inl w =>
      simpa only [substituteGraph,resizeGraph,SupportPorts.restricted,Equiv.refl_apply,Sum.map_inl]
        using restrict_edges s (C.system.graph.label v) (C.system.graph.edge v) (C.system.graph.direction_valid v) d (.inl w)
    | inr j => exact Fin.elim0 j

private def flatten_iso {A : RankedSet} {n : ℕ} {V W : Type}
    {G : Presentation (System A) n V} {H : Presentation (System A) n W}
    (f : FinitePresentations.PresentationIso G H) :
    FinitePresentations.PresentationIso (SupportPorts.flattened G) (SupportPorts.flattened H) :=
  UntrimmedFlattening.flattenGraphIso {
    vertex := f.vertex
    label := fun v => congrArg (fun a : Symbol (System A) => Sigma.mk a.1 (FinitePresentations.ofSetSystem a.2.val)) (f.label v)
    initial := f.initial
    root := f.root
    edge := f.edge }

private theorem expanded_eq {A : RankedSet} {m k : ℕ} (C : SetContext A m 0)
    (s : Fin k → Fin m) (R : System A k) :
    SupportPorts.expanded C.system.graph (fun v => arity k (C.system.graph.label v))
      (fun v => ports s (C.system.graph.label v)) (fun v => inner R (C.system.graph.label v)) =
      substituteGraph C.system.graph (Renaming.renameSystem s R) := by
  dsimp only [SupportPorts.expanded,substituteGraph]
  congr 1
  funext v
  exact expanded_label s R (C.system.graph.label v)

private theorem plug_flatten {A : RankedSet} {m : ℕ} (C : SetContext A m 0)
    (hC : C.system.Deterministic) (R : System A m) (U : System A 0)
    (hU : U.val = plug C R.val) :
    SystemFlattening (relabelSystem (SystemEvaluation.substituteSystem R) ⟨C.system,hC⟩) U := by
  have hv : (fun r a => (SystemEvaluation.substituteSystem R r a).val) = substitution R.val := by
    funext r a
    cases a with
    | inl a => rfl
    | inr e => obtain ⟨h⟩ := e; subst r; rfl
  change U.val = flatten (relabel (fun r a => (SystemEvaluation.substituteSystem R r a).val) C.system)
  rw [hv]; exact hU

private theorem plug_resize_canonical {A : RankedSet} {m k : ℕ} (C : SetContext A m 0)
    (hC : C.system.Deterministic) (s : Fin k → Fin m) (R : System A k)
    (U V : System A 0) (hU : U.val = plug C (Renaming.renameSystem s R).val)
    (hV : V.val = plug (resizeContext C s) R.val) : Morphisms.Isomorphic U.val V.val := by
  classical
  let a := fun v => arity k (C.system.graph.label v)
  let p := fun v => ports s (C.system.graph.label v)
  let f := fun v => inner R (C.system.graph.label v)
  obtain ⟨e⟩ := SupportPorts.flatten_iso C.system.graph a p f
  have hi := trim_iso e
  have hj := trim_iso (flatten_iso (restricted_iso C s R))
  have hexp := congrArg (fun G : Presentation (System A) 0 C.system.Vertex => trim (SupportPorts.flattened G)) (expanded_eq C s R)
  rw [hexp] at hi
  have hU' : U.val = trim (SupportPorts.flattened (substituteGraph C.system.graph (Renaming.renameSystem s R))) := by
    have hv : (fun r a => (SystemEvaluation.substituteSystem (Renaming.renameSystem s R) r a).val) =
        substitution (Renaming.renameSystem s R).val := by
      funext r a
      cases a with
      | inl a => rfl
      | inr e => obtain ⟨h⟩ := e; subst r; rfl
    change U.val = flatten (relabel (fun r a =>
      (SystemEvaluation.substituteSystem (Renaming.renameSystem s R) r a).val) C.system)
    rw [hv]
    exact hU
  rw [←hU'] at hi
  let G := substituteGraph (resizeGraph C s) R
  let Q := relabelSystem (SystemEvaluation.substituteSystem R) ⟨(resizeContext C s).system,resize_deterministic C hC s⟩
  have hQ : Q.val = trim G := rfl
  obtain ⟨i,hiC⟩ := hC.1
  have hrawdet : ∀ v d,d < (G.label v).1 → ∃! t,G.edge v d t := by
    intro v d hd
    -- The raw restricted graph has the same deterministic successors as its context.
    by_cases hh : IsHole (C.system.graph.label v)
    · have hk : d < k := by simpa only [G,substituteGraph,resizeGraph,new_hole_rank k _ hh] using hd
      have hs : (s ⟨d,hk⟩).val < (C.system.graph.label v).1 := by rw [old_hole_rank _ hh]; exact (s ⟨d,hk⟩).isLt
      obtain ⟨t,ht,hu⟩ := hC.2.2 v _ hs
      refine ⟨t,?_,?_⟩
      · change (if IsHole (C.system.graph.label v) then _ else _); rw [if_pos hh]; exact ⟨⟨d,hk⟩,rfl,ht⟩
      · intro u hu'
        change (if IsHole (C.system.graph.label v) then _ else _) at hu'
        rw [if_pos hh] at hu'
        obtain ⟨j,hj,hj'⟩ := hu'
        have he : j = ⟨d,hk⟩ := Fin.ext hj.symm
        subst j; exact hu u hj'
    · have hd' : d < (C.system.graph.label v).1 := by simpa only [G,substituteGraph,resizeGraph,symbol_rank k _ hh] using hd
      obtain ⟨t,ht,hu⟩ := hC.2.2 v d hd'
      exact ⟨t,by simpa only [G,substituteGraph,resizeGraph,if_neg hh] using ht,
        fun u hu' => hu u (by simpa only [G,substituteGraph,resizeGraph,if_neg hh] using hu')⟩
  have hv := SystemIsomorphisms.flatten_from_trim G i hiC hC.2.1 hrawdet Q hQ V
    (plug_flatten (resizeContext C s) (resize_deterministic C hC s) R V hV)
  exact SystemIsomorphisms.iso_trans (SystemIsomorphisms.iso_trans hi hj) (SystemIsomorphisms.iso_symm hv)


private theorem context_ext {A : RankedSet} {k n : ℕ} (C D : SetContext A k n)
    (h : C.system = D.system) : C = D := by
  cases C; cases D; cases h; rfl

/--
---
conclusion: Lax369799.ContextPorts.resize_exists
---
The hole stays reachable until its first visit, since all earlier edges
are unchanged. The reachable restriction has one hole and deterministic
successors in every new permitted direction.
-/
theorem resize_exists {A : RankedSet} {m k : ℕ} (C : SetContext A m 0)
    (hC : C.system.Deterministic) (s : Fin k → Fin m) :
    ∃ D : SetContext A k 0, D.system = trim (resizeGraph C s) ∧ D.system.Deterministic := by
  exact ⟨resizeContext C s,rfl,resize_deterministic C hC s⟩

/--
---
conclusion: Lax369799.ContextPorts.plug_resize
---
Restrict the matching outer directions while renaming the argument
ports. The raw flattenings are isomorphic; reachable restriction and
deterministic substitution preserve that isomorphism.
-/
theorem plug_resize {A : RankedSet} {m k : ℕ} (C : SetContext A m 0)
    (hC : C.system.Deterministic) (s : Fin k → Fin m) (R : System A k)
    (D : SetContext A k 0) (hD : D.system = trim (resizeGraph C s))
    (U V : System A 0) (hU : U.val = plug C (Renaming.renameSystem s R).val)
    (hV : V.val = plug D R.val) : Morphisms.Isomorphic U.val V.val := by
  have he : D = resizeContext C s := context_ext D _ hD
  rw [he] at hV
  exact plug_resize_canonical C hC s R U V hU hV

end Lax369799Proofs.ContextPorts
