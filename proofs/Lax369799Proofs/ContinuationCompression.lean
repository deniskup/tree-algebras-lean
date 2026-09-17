import Lax369799Proofs.DeterministicNormalForms
import Lax369799Proofs.Renaming
import Lax369799Proofs.ContextRelabelling
import Lax369799.ContextSmallification

set_option backward.isDefEq.respectTransparency false

namespace Lax369799Proofs.ContinuationCompression
open Lax369799.RankedSystems Lax369799.Flattening Lax369799.Morphisms
open Lax369799.Algebras Lax369799.Renaming Lax369799.Resolutions
open Lax369799.DeterministicNormalForms
open Lax369799Proofs.Pullbacks Lax369799Proofs.DeterministicNormalForms

def redirect {k : ℕ} (e : Fin k → Fin k) (d : ℕ) : ℕ :=
  if h : d < k then (e ⟨d, h⟩).val else 0

def slotMap {k : ℕ} (e : Fin k → Fin k) : Fin (k + 2) → Fin (k + 2) :=
  Fin.cases 0 (Fin.cases (0 : Fin (k + 1)).succ (fun i => (e i).succ.succ))

def rewiredGraph {A : RankedSet} {k : ℕ} (a : A k) (P : Fin (k + 1) → Option (A 1))
    (e : Fin k → Fin k) : Presentation A 0 (Fin (k + 2)) where
  label := label a P
  initial := {1}
  root := ∅
  edge := fun v d t => ∃ _hd : d < (label a P v).1,
    t = .inl (next a P v (redirect e d))
  direction_valid := fun _ _ _ h => h.choose

noncomputable def rewired {A : RankedSet} {k : ℕ} (a : A k)
    (P : Fin (k + 1) → Option (A 1)) (e : Fin k → Fin k) : System A 0 :=
  ⟨trim (rewiredGraph a P e), Yields.trim_deterministic _ 1 rfl rfl (by
    intro v d hd
    exact ⟨.inl (next a P v (redirect e d)), ⟨hd, rfl⟩,
      by rintro t ⟨h, rfl⟩; rfl⟩)⟩

private theorem slot_label {A : RankedSet} {k : ℕ} (a : A k)
    (P : Fin (k + 1) → Option (A 1)) (e : Fin k → Fin k)
    (hP : ∀ i, P (e i).succ = P i.succ) (v : Fin (k + 2)) :
    label a P (slotMap e v) = label a P v := by
  induction v using Fin.cases with
  | zero => rfl
  | succ i =>
    induction i using Fin.cases with
    | zero => rfl
    | succ i => simp only [slotMap, Fin.cases_succ, label, hP]

private theorem hole_next {k : ℕ} (e : Fin k → Fin k) (d : ℕ) (hd : d < k) :
    holeNext k (redirect e d) = slotMap e (holeNext k d) := by
  have he := (e ⟨d, hd⟩).isLt
  simp only [redirect, dif_pos hd, holeNext, dif_pos he]
  rfl

private theorem slot_next {A : RankedSet} {k : ℕ} (a : A k)
    (P : Fin (k + 1) → Option (A 1)) (e : Fin k → Fin k)
    (hP : ∀ i, P (e i).succ = P i.succ) (v : Fin (k + 2)) (d : ℕ)
    (hd : d < (label a P v).1) :
    next a P (slotMap e v) (redirect e d) = slotMap e (next a P v d) := by
  induction v using Fin.cases with
  | zero => exact hole_next e d hd
  | succ i =>
    induction i using Fin.cases with
    | zero =>
      cases h : P 0 with
      | none =>
        have hd' : d < k := by simpa only [label, Fin.cases_succ, h] using hd
        simpa only [slotMap, next, Fin.cases_succ, Fin.cases_zero, h, Option.elim_none]
          using hole_next e d hd'
      | some b => simp only [slotMap, next, Fin.cases_succ, Fin.cases_zero, h, Option.elim_some]
    | succ i =>
      cases h : P i.succ with
      | none =>
        have hd' : d < k := by simpa only [label, Fin.cases_succ, h] using hd
        simpa only [slotMap, next, Fin.cases_succ, hP, h, Option.elim_none]
          using hole_next e d hd'
      | some b => simp only [slotMap, next, Fin.cases_succ, hP, h, Option.elim_some, Fin.cases_zero]

noncomputable def collapseMap {A : RankedSet} {k : ℕ} (a : A k)
    (P : Fin (k + 1) → Option (A 1)) (e : Fin k → Fin k)
    (hP : ∀ i, P (e i).succ = P i.succ) : Map (graph a P) (rewiredGraph a P e) where
  toFun := slotMap e
  label := slot_label a P e hP
  initial := by intro v hv; change v = 1 at hv; subst v; rfl
  root := by intro v hv; exact False.elim hv
  edge := by
    rintro v d t ⟨hd, rfl⟩
    refine ⟨?_, ?_⟩
    · rw [slot_label a P e hP]
      exact hd
    · exact congrArg Sum.inl (slot_next a P e hP v d hd).symm

theorem evaluation_collapse {A : RankedSet} (E : Algebra A) (hE : UnfoldInvariant E)
    {k : ℕ} (a : A k) (P : Fin (k + 1) → Option (A 1)) (e : Fin k → Fin k)
    (hP : ∀ i, P (e i).succ = P i.succ) :
    E.eval 0 (pattern a P) = E.eval 0 (rewired a P e) := by
  let f : Morphism (pattern a P).val (rewired a P e).val := trimMap (collapseMap a P e hP)
  exact hE 0 _ _ ⟨(pattern a P).val,
    ⟨MorphismTheorems.identity _, MorphismTheorems.identity_surjective _⟩,
    ⟨f, MorphismTheorems.system_morphism_locally_surjective _ _ f⟩⟩

noncomputable def nestedGraph {A : RankedSet} {k : ℕ} (a : A k)
    (P : Fin (k + 1) → Option (A 1)) (e : Fin k → Fin k) :=
  graph (renameSystem e (atomicSystem a)) (fun i => (P i).map atomicSystem)

private theorem meta_label {A : RankedSet} {k : ℕ} (a : A k)
    (P : Fin (k + 1) → Option (A 1)) (e : Fin k → Fin k) (v : Fin (k + 2))
    (w : ((nestedGraph a P e).label v).2.val.Vertex) :
    (((nestedGraph a P e).label v).2.val.graph.label w) = label a P v := by
  induction v using Fin.cases with
  | zero => rfl
  | succ i =>
    cases hp : P i with
    | none =>
      have hl : (nestedGraph a P e).label i.succ = ⟨k, renameSystem e (atomicSystem a)⟩ := by
        simp only [nestedGraph, graph, label, Fin.cases_succ, hp, Option.map_none]
      rw [← cast_label hl w]
      simp only [label, Fin.cases_succ, hp]
      rfl
    | some b =>
      have hl : (nestedGraph a P e).label i.succ = ⟨1, atomicSystem b⟩ := by
        simp only [nestedGraph, graph, label, Fin.cases_succ, hp, Option.map_some]
      rw [← cast_label hl w]
      simp only [label, Fin.cases_succ, hp]
      rfl

private theorem meta_internal_false {A : RankedSet} {k : ℕ} (a : A k)
    (P : Fin (k + 1) → Option (A 1)) (e : Fin k → Fin k) (v : Fin (k + 2))
    (w u : ((nestedGraph a P e).label v).2.val.Vertex) (d : ℕ) :
    ¬ (((nestedGraph a P e).label v).2.val.graph.edge w d (.inl u)) := by
  intro ht
  induction v using Fin.cases with
  | zero => obtain ⟨s, ⟨j, hj, rfl⟩, he⟩ := ht; cases he
  | succ i =>
    cases hp : P i with
    | none =>
      have hl : (nestedGraph a P e).label i.succ = ⟨k, renameSystem e (atomicSystem a)⟩ := by
        simp only [nestedGraph, graph, label, Fin.cases_succ, hp, Option.map_none]
      obtain ⟨s, ⟨j, hj, rfl⟩, he⟩ := (cast_internal hl w u d).mpr ht
      cases he
    | some b =>
      have hl : (nestedGraph a P e).label i.succ = ⟨1, atomicSystem b⟩ := by
        simp only [nestedGraph, graph, label, Fin.cases_succ, hp, Option.map_some]
      obtain ⟨j, hj, he⟩ := (cast_internal hl w u d).mpr ht
      cases he

private theorem meta_exit {A : RankedSet} {k : ℕ} (a : A k)
    (P : Fin (k + 1) → Option (A 1)) (e : Fin k → Fin k) (v : Fin (k + 2))
    (w : ((nestedGraph a P e).label v).2.val.Vertex) (d : ℕ)
    (i : Fin ((nestedGraph a P e).label v).1)
    (hi : ((nestedGraph a P e).label v).2.val.graph.edge w d (.inr i)) :
    d < (label a P v).1 ∧
      next (renameSystem e (atomicSystem a)) (fun i => (P i).map atomicSystem) v i.val =
        next a P v (redirect e d) := by
  have hd : d < (label a P v).1 := by
    rw [← meta_label a P e v w]
    exact ((nestedGraph a P e).label v).2.val.graph.direction_valid _ _ _ hi
  refine ⟨hd, ?_⟩
  induction v using Fin.cases with
  | zero =>
    obtain ⟨s, ⟨j, hj, rfl⟩, he⟩ := hi
    have he : i = e j := Sum.inr.inj he
    have hj : d = j.val := hj
    subst d
    rw [he]
    simp only [next, Fin.cases_zero, redirect, dif_pos j.isLt]
  | succ r =>
    cases hp : P r with
    | none =>
      have hl : (nestedGraph a P e).label r.succ = ⟨k, renameSystem e (atomicSystem a)⟩ := by
        simp only [nestedGraph, graph, label, Fin.cases_succ, hp, Option.map_none]
      obtain ⟨s, ⟨j, hj, rfl⟩, he⟩ := (cast_exit hl w i d).mpr hi
      have he := congrArg Fin.val (Sum.inr.inj he)
      have hv := cast_variable_value hl i
      rw [hv] at he
      subst d
      rw [he]
      simp only [next, Fin.cases_succ, hp, Option.map_none, Option.elim_none, redirect, dif_pos j.isLt]
    | some b =>
      simp only [next, Fin.cases_succ, hp, Option.map_some, Option.elim_some]

noncomputable def flattenRewireMap {A : RankedSet} {k : ℕ} (a : A k)
    (P : Fin (k + 1) → Option (A 1)) (e : Fin k → Fin k) :
    Map (rawFlatten (nestedGraph a P e)) (rewiredGraph a P e) where
  toFun := Sigma.fst
  label := fun v => (meta_label a P e v.1 v.2).symm
  initial := fun _ h => h.1
  root := by
    intro v hv
    rcases hv with hv | ⟨hv, _⟩
    · change v.2 ∈ ((nestedGraph a P e).label v.1).2.val.graph.root at hv
      rw [((nestedGraph a P e).label v.1).2.property.2.1] at hv
      exact False.elim hv
    · exact False.elim hv
  edge := by
    intro v d t ht
    rcases ht with ⟨w, hw, _⟩ | ⟨i, hi, ht⟩
    · exact False.elim (meta_internal_false a P e v.1 v.2 w d hw)
    · obtain ⟨hd, he⟩ := meta_exit a P e v.1 v.2 d i hi
      rcases ht with ⟨w, hw, _, rfl⟩ | ⟨j, _, _⟩
      · obtain ⟨h, hw⟩ := hw
        refine ⟨hd, ?_⟩
        have hw := Sum.inl.inj hw
        change Sum.inl w.1 = .inl (next a P v.1 (redirect e d))
        exact congrArg Sum.inl (hw.trans he)
      · exact Fin.elim0 j

theorem evaluation_rewire {A : RankedSet} (E : Algebra A) (hE : UnfoldInvariant E)
    {k : ℕ} (a : A k) (P : Fin (k + 1) → Option (A 1)) (e : Fin k → Fin k) :
    E.eval 0 (pattern (E.eval k (renameSystem e (atomicSystem a))) P) =
      E.eval 0 (rewired a P e) := by
  let T := pattern (renameSystem e (atomicSystem a)) (fun i => (P i).map atomicSystem)
  obtain ⟨U, hU⟩ := Flattening.flatten_system T
  have f : Morphism U.val (rewired a P e).val := by
    rw [hU]
    exact trimMap (compose (flattenEmbedding (nestedGraph a P e)) (flattenRewireMap a P e))
  have he := hE 0 U (rewired a P e) ⟨U.val,
    ⟨MorphismTheorems.identity _, MorphismTheorems.identity_surjective _⟩,
    ⟨f, MorphismTheorems.system_morphism_locally_surjective _ _ f⟩⟩
  have ha := E.associative 0 T U hU
  have hp := pattern_relabel E hE E.eval (renameSystem e (atomicSystem a))
    (fun i => (P i).map atomicSystem)
  have hP : (fun i => ((P i).map atomicSystem).map (E.eval 1)) = P := by
    funext i
    cases h : P i with
    | none => rfl
    | some b => exact congrArg some (E.unit 1 b)
  rw [hP] at hp
  exact hp.symm.trans (ha.trans he)

theorem pattern_compression {A : RankedSet} (E : Algebra A) (hE : UnfoldInvariant E)
    {k : ℕ} (a : A k) (P : Fin (k + 1) → Option (A 1)) (e : Fin k → Fin k)
    (hP : ∀ i, P (e i).succ = P i.succ) :
    E.eval 0 (pattern a P) =
      E.eval 0 (pattern (E.eval k (renameSystem e (atomicSystem a))) P) :=
  (evaluation_collapse E hE a P e hP).trans (evaluation_rewire E hE a P e).symm

theorem context_compression {A : RankedSet} (E : Algebra A) (hE : UnfoldInvariant E)
    {k : ℕ} (C : SetContext A k 0) (hC : C.system.Deterministic) (S : System A k)
    (e : Fin k → Fin k)
    (hP : ∀ i, (Lax369799.DeterministicPieces.continuation C (e i).succ).map (E.eval 1) =
      (Lax369799.DeterministicPieces.continuation C i.succ).map (E.eval 1)) :
    ∃ U V : System A 0, U.val = plug C S.val ∧ V.val = plug C (renameSystem e S).val ∧
      E.eval 0 U = E.eval 0 V := by
  obtain ⟨U, hU, heU⟩ := SystemEvaluation.context_evaluation E C hC S
  obtain ⟨V, hV, heV⟩ := SystemEvaluation.context_evaluation E C hC (renameSystem e S)
  refine ⟨U, V, hU, hV, ?_⟩
  let P := fun i => (Lax369799.DeterministicPieces.continuation C i).map (E.eval 1)
  calc
    E.eval 0 U = E.eval 0 (pattern (E.eval k S) P) :=
      heU.trans (evaluated_normal_form E hE C hC (E.eval k S))
    _ = E.eval 0 (pattern (E.eval k (renameSystem e S)) P) := by
      rw [SystemEvaluation.rename_evaluation E hE e S]
      exact pattern_compression E hE (E.eval k S) P e hP
    _ = E.eval 0 V :=
      (heV.trans (evaluated_normal_form E hE C hC (E.eval k (renameSystem e S)))).symm

/--
---
conclusion: Lax369799.ContextSmallification.context_smallification
---
Compress by target and optional unary evaluation. Optional observations
preserve the direct-loop case. The deterministic normal form turns their
equality into equality of context values after variable redirection.
-/
theorem context_smallification {A : RankedSet} (E : Algebra A) (hE : UnfoldInvariant E)
    [Finite (A 1)] {m n : ℕ} (C : SetContext A m 0) (hC : C.system.Deterministic)
    (S : System A m) (σ : Fin m → Fin n) :
    ∃ (m' : ℕ) (τ : Fin m → Fin m') (sectionMap : Fin m' → Fin m),
      (∀ j, τ (sectionMap j) = j) ∧
      (∀ i, σ (sectionMap (τ i)) = σ i) ∧
      (∀ j, Nat.card {i // σ (sectionMap i) = j} ≤ Nat.card (A 1) + 1) ∧
      ∃ U V : System A 0,
        U.val = plug C S.val ∧
        V.val = plug C (renameSystem (sectionMap ∘ τ) S).val ∧
        E.eval 0 U = E.eval 0 V := by
  obtain ⟨m', τ, sectionMap, hs, hσ, ho, _, hb⟩ :=
    DeterministicPieces.compress_continuations C hC σ (E.eval 1)
  exact ⟨m', τ, sectionMap, hs, hσ, hb,
    context_compression E hE C hC S (sectionMap ∘ τ) ho⟩

/--
---
conclusion: Lax369799.ContextSmallification.mapped_context_smallification
---
Relabel the context and argument into the observing algebra, apply
smallification there, and use commutation of relabelling with plugging
to recover the two substituted systems over the original alphabet.
-/
theorem mapped_context_smallification {A B : RankedSet} (E : Algebra B) (hE : UnfoldInvariant E)
    [Finite (B 1)] (η : RankedMap A B) {m n : ℕ}
    (C : SetContext A m 0) (hC : C.system.Deterministic) (S : System A m) (σ : Fin m → Fin n) :
    ∃ (m' : ℕ) (τ : Fin m → Fin m') (sectionMap : Fin m' → Fin m),
      (∀ j, τ (sectionMap j) = j) ∧
      (∀ i, σ (sectionMap (τ i)) = σ i) ∧
      (∀ j, Nat.card {i // σ (sectionMap i) = j} ≤ Nat.card (B 1) + 1) ∧
      ∃ U V : System A 0,
        U.val = plug C S.val ∧
        V.val = plug C (renameSystem (sectionMap ∘ τ) S).val ∧
        E.eval 0 (relabelSystem η U) = E.eval 0 (relabelSystem η V) := by
  let D := Lax369799.ContextRelabelling.mapContext η C
  have hD : D.system.Deterministic :=
    (relabelSystem (Lax369799.ContextRelabelling.mapAlphabet η m) ⟨C.system, hC⟩).property
  obtain ⟨m', τ, sectionMap, hs, hσ, hb, U', V', hU', hV', he⟩ :=
    context_smallification E hE D hD (relabelSystem η S) σ
  obtain ⟨U, hU⟩ := ContextRelabelling.plug_system C hC S
  obtain ⟨V, hV⟩ := ContextRelabelling.plug_system C hC (renameSystem (sectionMap ∘ τ) S)
  have hu : relabelSystem η U = U' := by
    apply Subtype.ext
    change relabel η U.val = U'.val
    rw [hU, ContextRelabelling.relabel_plug]
    exact hU'.symm
  have hv : relabelSystem η V = V' := by
    apply Subtype.ext
    change relabel η V.val = V'.val
    rw [hV, ContextRelabelling.relabel_plug]
    exact hV'.symm
  exact ⟨m', τ, sectionMap, hs, hσ, hb, U, V, hU, hV, by rw [hu, hv]; exact he⟩

end Lax369799Proofs.ContinuationCompression
