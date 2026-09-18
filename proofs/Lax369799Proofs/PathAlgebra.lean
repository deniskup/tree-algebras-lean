import Lax369799.PathAlgebra
import Lax369799Proofs.Flattening

set_option backward.isDefEq.respectTransparency false
namespace Lax369799Proofs.PathAlgebra
open Lax369799.RankedSystems Lax369799.Algebras Lax369799.InitialAlgebra
open Lax369799.PathAlgebra Lax369799.Flattening Lax369799.Morphisms
open Lax369799Proofs.Pullbacks

private theorem initial_spec {A : RankedSet} {n : ℕ} (S : System A n) :
    S.val.graph.initial = {initial S} := Classical.choose_spec S.property.1

private theorem initial_mem {A : RankedSet} {n : ℕ} (S : System A n) :
    initial S ∈ S.val.graph.initial := by rw [initial_spec]; rfl

private theorem initial_unique {A : RankedSet} {n : ℕ} (S : System A n) {v : S.val.Vertex}
    (h : v ∈ S.val.graph.initial) : v = initial S := by rwa [initial_spec] at h

private theorem map_run {Q V W : Type} {n : ℕ} {G : Presentation (Carrier Q) n V}
    {H : Presentation (Carrier Q) n W} (f : V → W)
    (hl : ∀ v, H.label (f v) = G.label v)
    (he : ∀ v d t, G.edge v d t → H.edge (f v) d (Sum.map f id t))
    {v q out} (h : Run G v q out) : Run H (f v) q out := by
  induction h with
  | halt h => exact .halt (by simpa only [hl] using h)
  | exit d h hed => exact .exit d (by simpa only [hl] using h) (he _ _ _ hed)
  | step d h hed _ ih => exact .step d (by simpa only [hl] using h) (he _ _ _ hed) ih

private theorem trim_run {Q V : Type} {n : ℕ} [Fintype V]
    (G : Presentation (Carrier Q) n V) (v : (trim G).Vertex) (q : Q) (out : Result Q n) :
    Run (trim G).graph v q out ↔ Run G (vertex G v) q out := by
  constructor
  · exact map_run (vertex G) (fun _ => rfl) (fun _ _ _ h => h)
  · intro h
    generalize hv : vertex G v = w at h
    induction h generalizing v with
    | halt h => exact .halt (by change Halt (G.label (vertex G v)) _ _; rwa [hv])
    | exit d h he =>
      exact .exit d (by change Exit (G.label (vertex G v)) _ _ _; rwa [hv])
        (by change G.edge (vertex G v) _ _; rwa [hv])
    | @step w u q r out d h he ht ih =>
      have hu : G.Reachable u := by
        obtain ⟨a, ha, hp⟩ := ((index G).symm v).property
        exact ⟨a, ha, hp.tail ⟨d, by change G.edge (vertex G v) _ _; rwa [hv]⟩⟩
      let u' := index G ⟨u, hu⟩
      have hue : vertex G u' = u := vertex_index G u hu
      refine .step d (by change Exit (G.label (vertex G v)) _ _ _; rwa [hv]) ?_ (ih u' hue)
      change G.edge (vertex G v) d (.inl (vertex G u'))
      rw [hv, hue]
      exact he

private theorem pull_run {Q : Type} {n : ℕ} {S T : SetSystem (Carrier Q) n}
    (f : Morphism S T) (hf : f.LocallySurjective) {v q out}
    (h : Run T.graph (f.toFun v) q out) : Run S.graph v q out := by
  generalize hv : f.toFun v = w at h
  induction h generalizing v with
  | halt h =>
    apply Run.halt
    rw [← f.label, hv]
    exact h
  | @exit w q r i d h he =>
    have he' : T.graph.edge (f.toFun v) d (.inr i) := hv.symm ▸ he
    obtain ⟨t, ht, heq⟩ := hf.2.2 v d _ he'
    cases t with
    | inl u => cases heq
    | inr j =>
      cases heq
      exact .exit d (by rw [← f.label, hv]; exact h) ht
  | @step w u q r out d h he _ ih =>
    have he' : T.graph.edge (f.toFun v) d (.inl u) := hv.symm ▸ he
    obtain ⟨t, ht, heq⟩ := hf.2.2 v d _ he'
    cases t with
    | inl u' =>
      have hu : f.toFun u' = u := Sum.inl.inj heq
      exact .step d (by rw [← f.label, hv]; exact h) ht (ih hu)
    | inr j => cases heq

private theorem unit_value {Q : Type} (n : ℕ) (a : Carrier Q n) :
    Lax369799.PathAlgebra.evaluate n (atomicSystem a) = a := by
  funext q
  ext out
  change Run (atomic a).graph _ q out ↔ out ∈ a q
  constructor
  · intro h
    cases h with
    | halt h => exact h
    | @exit v q r i d h he =>
      obtain ⟨j, hd, heq⟩ := he
      have hji : i = j := Sum.inr.inj heq
      subst i
      obtain ⟨k, hk, hh⟩ := h
      have hkj : k = j := Fin.ext (hk.trans hd)
      subst k
      exact hh
    | step d h he ht => obtain ⟨j, _, heq⟩ := he; cases heq
  · intro h
    cases out with
    | inl r => exact .halt h
    | inr ir =>
      obtain ⟨i, r⟩ := ir
      exact .exit i.val ⟨i, rfl, h⟩ ⟨i, rfl, rfl⟩

private noncomputable abbrev raw {Q : Type} {n : ℕ} (S : System (System (Carrier Q)) n) :=
  Flattening.graph (relabel (fun _ T => T.val) S.val)

private def Finish {Q : Type} {n : ℕ} (S : System (System (Carrier Q)) n)
    (F : S.val.Vertex → Q → Result Q n → Prop) (v : S.val.Vertex)
    (y : Result Q (S.val.graph.label v).1) (out : Result Q n) : Prop :=
  match y with
  | .inl r => out = .inl r
  | .inr (i, r) => ∃ t, S.val.graph.edge v i.val t ∧
      match t with
      | .inl w => F w r out
      | .inr j => out = .inr (j, r)

private theorem lift_inner {Q : Type} {n : ℕ} (S : System (System (Carrier Q)) n)
    (v : S.val.Vertex) {u q y} (h : Run (S.val.graph.label v).2.val.graph u q y)
    (out : Result Q n)
    (hf : Finish S (fun w r z => Run (raw S) ⟨w, initial (S.val.graph.label w).2⟩ r z) v y out) :
    Run (raw S) ⟨v, u⟩ q out := by
  induction h with
  | halt h => subst out; exact .halt h
  | @exit u q r i d h he =>
    obtain ⟨t, ht, hf⟩ := hf
    cases t with
    | inl w =>
      exact .step d h (.inr ⟨i, he, .inl ⟨⟨w, initial (S.val.graph.label w).2⟩,
        ht, initial_mem _, rfl⟩⟩) hf
    | inr j =>
      subst out
      exact .exit d h (.inr ⟨i, he, .inr ⟨j, ht, rfl⟩⟩)
  | step d h he _ ih =>
    exact .step d h (.inl ⟨_, he, rfl⟩) (ih hf)

private theorem expand_run {Q : Type} {n : ℕ} (S : System (System (Carrier Q)) n)
    {v q out} (h : Run (relabelSystem Lax369799.PathAlgebra.evaluate S).val.graph v q out) :
    Run (raw S) ⟨v, initial (S.val.graph.label v).2⟩ q out := by
  induction h with
  | halt h => exact lift_inner S _ h _ rfl
  | @exit v q r i d h he =>
    obtain ⟨j, rfl, hj⟩ := h
    exact lift_inner S v hj _ ⟨.inr i, he, rfl⟩
  | @step v w q r out d h he _ ih =>
    obtain ⟨j, rfl, hj⟩ := h
    exact lift_inner S v hj _ ⟨.inl w, he, ih⟩

private theorem finish_outer {Q : Type} {n : ℕ} (S : System (System (Carrier Q)) n)
    {v q y out} (h : Run (S.val.graph.label v).2.val.graph (initial (S.val.graph.label v).2) q y)
    (hf : Finish S (fun w r z => Run (relabelSystem Lax369799.PathAlgebra.evaluate S).val.graph w r z) v y out) :
    Run (relabelSystem Lax369799.PathAlgebra.evaluate S).val.graph v q out := by
  cases y with
  | inl r => subst out; exact .halt h
  | inr ir =>
    obtain ⟨i, r⟩ := ir
    obtain ⟨t, ht, hf⟩ := hf
    cases t with
    | inl w => exact .step i.val ⟨i, rfl, h⟩ ht hf
    | inr j => subst out; exact .exit i.val ⟨i, rfl, h⟩ ht

private theorem contract_local {Q : Type} {n : ℕ} (S : System (System (Carrier Q)) n)
    {v q out} (h : Run (raw S) v q out) :
    ∃ y, Run (S.val.graph.label v.1).2.val.graph v.2 q y ∧
      Finish S (fun w r z => Run (relabelSystem Lax369799.PathAlgebra.evaluate S).val.graph w r z) v.1 y out := by
  induction h with
  | halt h => exact ⟨_, .halt h, rfl⟩
  | @exit v q r j d h he =>
    rcases he with ⟨w, hw, hh⟩ | ⟨i, hi, hh⟩
    · cases hh
    · rcases hh with ⟨w, hw, hiw, hh⟩ | ⟨k, hk, hh⟩
      · cases hh
      · cases hh
        exact ⟨_, .exit d h hi, .inr j, hk, rfl⟩
  | @step v w q r out d h he _ ih =>
    rcases he with ⟨u, hu, hh⟩ | ⟨i, hi, hh⟩
    · cases hh
      obtain ⟨y, hy, hf⟩ := ih
      exact ⟨y, .step d h hu hy, hf⟩
    · rcases hh with ⟨w', hw, hiw, hh⟩ | ⟨k, hk, hh⟩
      · cases hh
        obtain ⟨y, hy, hf⟩ := ih
        have hwi : w.2 = initial (S.val.graph.label w.1).2 := initial_unique _ hiw
        rw [hwi] at hy
        exact ⟨_, .exit d h hi, .inl w.1, hw, finish_outer S hy hf⟩
      · cases hh

private theorem flatten_run {Q : Type} {n : ℕ} (S : System (System (Carrier Q)) n)
    (v : S.val.Vertex) (q : Q) (out : Result Q n) :
    Run (relabelSystem Lax369799.PathAlgebra.evaluate S).val.graph v q out ↔
      Run (raw S) ⟨v, initial (S.val.graph.label v).2⟩ q out := by
  refine ⟨expand_run S, ?_⟩
  intro h
  obtain ⟨y, hy, hf⟩ := contract_local S h
  exact finish_outer S hy hf

/--
---
conclusion: Lax369799.PathAlgebra.algebra
---
A finite execution in a flattening can be partitioned into inner
executions, and conversely inner executions expand to flattened paths.
Reachable restriction preserves executions from the initial vertex.
-/
theorem algebra (Q : Type) : ∃ E : Algebra (Carrier Q), E.eval = Lax369799.PathAlgebra.evaluate := by
  classical
  refine ⟨{
    eval := Lax369799.PathAlgebra.evaluate
    isomorphic := ?_
    unit := unit_value
    associative := ?_ }, rfl⟩
  · intro n S T h
    obtain ⟨f, _, hf⟩ := h
    have hi : f.toFun (initial S) = initial T := initial_unique T (f.initial _ (initial_mem S))
    funext q
    ext out
    change Run S.val.graph (initial S) q out ↔ Run T.val.graph (initial T) q out
    rw [← hi]
    exact ⟨map_run f.toFun f.label f.edge, pull_run f hf⟩
  · intro n S T ht
    let G := raw S
    have htv : T.val = trim G := ht
    have hd : (trim G).Deterministic := htv ▸ T.property
    have hte : T = ⟨trim G, hd⟩ := Subtype.ext htv
    subst T
    let v := initial (⟨trim G, hd⟩ : System (Carrier Q) n)
    have hv : vertex G v ∈ G.initial := initial_mem (⟨trim G, hd⟩ : System (Carrier Q) n)
    have ho : (vertex G v).1 = initial S := initial_unique S hv.1
    have hi : (vertex G v).2 = initial (S.val.graph.label (vertex G v).1).2 := initial_unique _ hv.2
    have hp : vertex G v = ⟨initial S, initial (S.val.graph.label (initial S)).2⟩ := by
      calc
        vertex G v = ⟨(vertex G v).1, initial (S.val.graph.label (vertex G v).1).2⟩ :=
          Sigma.ext rfl (heq_of_eq hi)
        _ = _ := by rw [ho]
    funext q
    ext out
    change Run (relabelSystem Lax369799.PathAlgebra.evaluate S).val.graph (initial S) q out ↔
      Run (trim G).graph v q out
    rw [trim_run, hp]
    exact flatten_run S (initial S) q out

/--
---
conclusion: Lax369799.PathAlgebra.finite_carrier
---
A finite state set gives finitely many relations at each finite arity.
-/
theorem finite_carrier (Q : Type) [Finite Q] : RankwiseFinite (Carrier Q) := by
  classical
  intro n
  let : Fintype Q := Fintype.ofFinite Q
  unfold Carrier Result
  infer_instance

end Lax369799Proofs.PathAlgebra
