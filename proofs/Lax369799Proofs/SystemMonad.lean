import Lax369799.SystemMonad
import Lax369799Proofs.SubstitutionProfiles
import Lax369799Proofs.SystemSubstitution

namespace Lax369799Proofs.SystemMonad
set_option backward.isDefEq.respectTransparency false
open Lax369799
open RankedSystems Morphisms
open Lax369799Proofs.Pullbacks Lax369799Proofs.DeterministicNormalForms
open Lax369799Proofs.SystemIsomorphisms

/--
---
conclusion: Lax369799.SystemMonad.outer_unit
---
-/
theorem outer_unit {A : RankedSet} {n : ℕ} (S : System A n) (U : System A n)
    (hU : Flattening.SystemFlattening (atomicSystem S) U) : Isomorphic U.val S.val := by
  have hid {B : RankedSet} (S : System B n) : Renaming.renameSystem id S = S := by
    apply Subtype.ext
    exact Renaming.rename_identity S.val
  have hU' : Flattening.SystemFlattening (Renaming.renameSystem id (atomicSystem S)) U := by
    rw [hid]; exact hU
  have h := renamed_iso id S U hU'
  rwa [hid] at h

private noncomputable def trimProjection {A : RankedSet} {n : ℕ} {V : Type} [Fintype V]
    (G : Presentation A n V) : Map (trim G).graph G where
  toFun := vertex G
  initial := fun _ h => h
  root := fun _ h => h
  label := fun _ => rfl
  edge := fun _ _ _ h => h

private def innerUnitMap {A : RankedSet} {n : ℕ} (S : System A n) :
    Map (rawFlatten (relabelSystem (fun _ a => atomicSystem a) S).val.graph) S.val.graph where
  toFun := Sigma.fst
  initial := fun _ h => h.1
  root := by intro v h; exact h.elim (fun h => h.elim) And.left
  label := fun _ => rfl
  edge := by
    intro v d t h
    rcases h with ⟨w,⟨i,hi,he⟩,_⟩ | ⟨i,⟨j,hd,he⟩,h⟩
    · cases he
    · have hij : i = j := Sum.inr.inj he
      subst j
      subst d
      rcases h with ⟨w,hw,_,rfl⟩ | ⟨j,hj,rfl⟩ <;> assumption

/--
---
conclusion: Lax369799.SystemMonad.inner_unit
---
-/
theorem inner_unit {A : RankedSet} {n : ℕ} (S : System A n) (U : System A n)
    (hU : Flattening.SystemFlattening (relabelSystem (fun _ a => atomicSystem a) S) U) :
    Isomorphic U.val S.val := by
  classical
  let G := rawFlatten (relabelSystem (fun _ a => atomicSystem a) S).val.graph
  change U.val = trim G at hU
  have hd : (trim G).Deterministic := hU ▸ U.property
  rw [hU]
  apply injective_isomorphic ⟨trim G,hd⟩ S (project (innerUnitMap S))
  intro a b h
  apply vertex_injective G
  apply Sigma.ext h
  apply heq_of_eq
  apply Fin.ext
  have ha : (vertex G a).2.val < 1 := (vertex G a).2.isLt
  have hb : (vertex G b).2.val < 1 := (vertex G b).2.isLt
  change (vertex G a).2.val = (vertex G b).2.val
  omega

/--
---
conclusion: Lax369799.SystemMonad.associative
---
-/
theorem associative {A : RankedSet} {n : ℕ} (P : System (System (System A)) n)
    (Q : System (System A) n) (U : System A n)
    (t : ∀ v : P.val.Vertex, System A (P.val.graph.label v).1) (W : System A n)
    (hQ : Flattening.SystemFlattening P Q)
    (hU : Flattening.SystemFlattening Q U)
    (ht : ∀ v, Flattening.SystemFlattening (P.val.graph.label v).2 (t v))
    (hW : Flattening.SystemFlattening (PolynomialContexts.withLabels P t) W) :
    Isomorphic U.val W.val := by
  classical
  let G := P.val.graph
  let M := fun v : P.val.Vertex => (P.val.graph.label v).2.val.graph
  let L := rawFlatten (rawFlatten G)
  obtain ⟨r,hr⟩ := P.property.1
  obtain ⟨⟨z,hz⟩,hroot⟩ := raw_marks G r hr P.property.2.1
  have htotal := raw_total G P.property.2.2
  let Z : System A n := ⟨trim L,RawSystemFlattening.deterministic (rawFlatten G) z hz hroot htotal⟩
  have hQ' : Q.val = trim (rawFlatten G) := hQ
  have hUL := flatten_from_trim (rawFlatten G) z hz hroot htotal Q hQ' U hU
  have htv : ∀ v, (t v).val = trim (rawFlatten (M v)) := ht
  let tc : ∀ v, System A (P.val.graph.label v).1 := fun v =>
    ⟨trim (rawFlatten (M v)),htv v ▸ (t v).property⟩
  have htc : t = tc := funext (fun v => Subtype.ext (htv v))
  rw [htc] at hW
  let innerMap := fun v => trimProjection (rawFlatten (M v))
  let f := UntrimmedFlattening.substituteMap G
    (fun v => (trim (rawFlatten (M v))).graph) (fun v => rawFlatten (M v)) innerMap
  let assoc := UntrimmedFlattening.substituteAssoc G M (fun v w => ((M v).label w).2.val.graph)
  let g := UntrimmedFlattening.isoMap (UntrimmedFlattening.isoSymm assoc)
  let fg := Lax369799Proofs.DeterministicNormalForms.compose f g
  have hf : Function.Injective f.toFun := by
    intro a b h
    obtain ⟨v,a⟩ := a
    obtain ⟨w,b⟩ := b
    have hvw : v = w := congrArg Sigma.fst h
    subst w
    have hab : vertex (rawFlatten (M v)) a = vertex (rawFlatten (M v)) b :=
      eq_of_heq (Sigma.mk.inj_iff.mp h).2
    have he := vertex_injective (rawFlatten (M v)) hab
    subst b
    rfl
  have hfg : Function.Injective fg.toFun := assoc.vertex.symm.injective.comp hf
  let H := rawFlatten (PolynomialContexts.withLabels P tc).val.graph
  have hW' : W.val = trim H := hW
  have hdH : (trim H).Deterministic := hW' ▸ W.property
  have hWL : Isomorphic W.val Z.val := by
    rw [hW']
    exact injective_isomorphic ⟨trim H,hdH⟩ Z (trimMap fg) (trimMap_injective fg hfg)
  exact iso_trans hUL (iso_symm hWL)

private theorem sum_map_inj {V W : Type} {n : ℕ} (f : V → W)
    (hf : Function.Injective f) : Function.Injective (Sum.map f (id : Fin n → Fin n)) := by
  intro a b h
  cases a <;> cases b <;> simp_all
  exact hf h

private noncomputable def presentation_iso {A : RankedSet} {n : ℕ} {S T : SetSystem A n}
    (f : Morphism S T) (hf : Function.Bijective f.toFun) (hc : f.LocallySurjective) :
    FinitePresentations.PresentationIso S.graph T.graph where
  vertex := Equiv.ofBijective f.toFun hf
  label := f.label
  initial := by
    intro v
    constructor
    · intro h
      obtain ⟨u,hu,he⟩ := hc.1 (f.toFun v) h
      exact hf.1 he ▸ hu
    · exact f.initial v
  root := by
    intro v
    constructor
    · intro h
      obtain ⟨u,hu,he⟩ := hc.2.1 (f.toFun v) h
      exact hf.1 he ▸ hu
    · exact f.root v
  edge := by
    intro v d t
    constructor
    · intro h
      obtain ⟨u,hu,he⟩ := hc.2.2 v d (Sum.map f.toFun id t) h
      exact sum_map_inj f.toFun hf.1 he ▸ hu
    · exact f.edge v d t

/--
---
conclusion: Lax369799.SystemMonad.flatten_isomorphic
---
-/
theorem flatten_isomorphic {A : RankedSet} {n : ℕ}
    (P Q : System (System A) n) (U W : System A n)
    (hP : Flattening.SystemFlattening P U) (hQ : Flattening.SystemFlattening Q W)
    (h : Isomorphic P.val Q.val) : Isomorphic U.val W.val := by
  obtain ⟨f,hf,hc⟩ := h
  let η : RankedMap (System A) (FinitePresentations.FiniteSystem A) :=
    fun _ S => FinitePresentations.ofSetSystem S.val
  let g := SystemSubstitution.relabelMorphism η f
  let I := presentation_iso g hf hc
  let F := UntrimmedFlattening.flattenGraphIso I
  change U.val = trim (rawFlatten P.val.graph) at hP
  change W.val = trim (rawFlatten Q.val.graph) at hQ
  have hdP : (trim (rawFlatten P.val.graph)).Deterministic := hP ▸ U.property
  have hdQ : (trim (rawFlatten Q.val.graph)).Deterministic := hQ ▸ W.property
  rw [hP,hQ]
  exact trim_isomorphic F hdP hdQ

end Lax369799Proofs.SystemMonad
