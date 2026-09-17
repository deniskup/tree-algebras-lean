import Lax369799Proofs.DeterministicPieces
import Lax369799Proofs.SystemEvaluation
import Lax369799.DeterministicNormalForms
import Lax369799.FinitePresentations

set_option backward.isDefEq.respectTransparency false

namespace Lax369799Proofs.DeterministicNormalForms
open Lax369799.RankedSystems Lax369799.Flattening Lax369799.Morphisms
open Lax369799.ContextDecomposition Lax369799.AlgebraicDecomposition
open Lax369799.DeterministicNormalForms
open Lax369799.DeterministicPieces
open Lax369799Proofs.Pullbacks

noncomputable def pattern {A : RankedSet} {k : ℕ} (a : A k)
    (P : Fin (k + 1) → Option (A 1)) : System A 0 :=
  ⟨trim (graph a P), Yields.trim_deterministic _ 1 rfl rfl (by
    intro v d hd
    exact ⟨.inl (next a P v d), ⟨hd, rfl⟩, by rintro t ⟨h, rfl⟩; rfl⟩)⟩

noncomputable def rawFlatten {A : RankedSet} {n : ℕ} {V : Type}
    (G : Presentation (System A) n V) :
    Presentation A n ((v : V) × (G.label v).2.val.Vertex) :=
  Lax369799.FinitePresentations.flattenPresentation {
    G with label := fun v => ⟨(G.label v).1,
      Lax369799.FinitePresentations.ofSetSystem (G.label v).2.val⟩ }

noncomputable def flattenEmbedding {A : RankedSet} {n : ℕ} {V : Type} [Fintype V]
    (G : Presentation (System A) n V) :
    Map (Flattening.graph (relabel (fun _ (S : System A _) => S.val) (trim G))) (rawFlatten G) where
  toFun := fun v => ⟨vertex G v.1, by exact v.2⟩
  label := fun _ => rfl
  initial := by intro v h; exact ⟨h.1, h.2⟩
  root := by
    intro v h
    rcases h with h | ⟨h, hi⟩
    · exact Or.inl h
    · exact Or.inr ⟨h, hi⟩
  edge := by
    intro v d t ht
    rcases ht with ⟨w, hw, rfl⟩ | ⟨i, hi, ht⟩
    · exact Or.inl ⟨w, hw, rfl⟩
    · refine Or.inr ⟨i, hi, ?_⟩
      rcases ht with ⟨w, hw, hw', rfl⟩ | ⟨j, hj, rfl⟩
      · exact Or.inl ⟨⟨vertex G w.1, by exact w.2⟩, hw, by exact hw', rfl⟩
      · exact Or.inr ⟨j, hj, rfl⟩

noncomputable def componentPosition {A : RankedSet} {k : ℕ}
    (C : SetContext A k 0) (a : A k) (j : Fin (k + 2))
    (w : (label (atomicSystem a) (continuation C) j).2.val.Vertex) : C.system.Vertex := by
  classical
  induction j using Fin.cases with
  | zero => exact holeVertex C
  | succ i =>
    by_cases h : (trim (ordinaryPiece C i)).Deterministic
    · have hc : continuation C i = some ⟨trim (ordinaryPiece C i), h⟩ := by
        unfold continuation; rw [dif_pos h]
      have w' : (trim (ordinaryPiece C i)).Vertex := by
        have hl : label (atomicSystem a) (continuation C) i.succ =
            ⟨1, ⟨trim (ordinaryPiece C i), h⟩⟩ := by simp only [label, Fin.cases_succ, hc]
        exact cast (congrArg (fun b : Symbol (System A) => b.2.val.Vertex) hl) w
      exact (vertex (ordinaryPiece C i) w').val
    · exact holeVertex C

noncomputable def position {A : RankedSet} {k : ℕ} (C : SetContext A k 0) (a : A k)
    (v : (j : Fin (k + 2)) × (label (atomicSystem a) (continuation C) j).2.val.Vertex) :
    C.system.Vertex := componentPosition C a v.1 v.2

theorem cast_label {A : RankedSet} {b c : Symbol (System A)} (h : b = c)
    (w : b.2.val.Vertex) :
    c.2.val.graph.label (cast (congrArg (fun q : Symbol (System A) => q.2.val.Vertex) h) w) =
      b.2.val.graph.label w := by
  cases h
  rfl

private theorem hole_label {A : RankedSet} {k : ℕ} (C : SetContext A k 0) (a : A k) :
    (relabel (Lax369799.SystemEvaluation.fillLetter a) C.system).graph.label (holeVertex C) =
      ⟨k, a⟩ := by
  change (⟨(C.system.graph.label (holeVertex C)).1,
    Lax369799.SystemEvaluation.fillLetter a _ (C.system.graph.label (holeVertex C)).2⟩ : Symbol A) = _
  rw [ContextDecomposition.hole_label]; rfl

private theorem position_label {A : RankedSet} {k : ℕ} (C : SetContext A k 0) (a : A k)
    (v : (j : Fin (k + 2)) × (label (atomicSystem a) (continuation C) j).2.val.Vertex) :
    (relabel (Lax369799.SystemEvaluation.fillLetter a) C.system).graph.label (position C a v) =
      (rawFlatten (graph (atomicSystem a) (continuation C))).label v := by
  classical
  obtain ⟨j, w⟩ := v
  change _ = (label (atomicSystem a) (continuation C) j).2.val.graph.label w
  induction j using Fin.cases with
  | zero => exact hole_label C a
  | succ i =>
    by_cases h : (trim (ordinaryPiece C i)).Deterministic
    · have hc : continuation C i = some ⟨trim (ordinaryPiece C i), h⟩ := by
        unfold continuation; rw [dif_pos h]
      have hl : label (atomicSystem a) (continuation C) i.succ =
          ⟨1, ⟨trim (ordinaryPiece C i), h⟩⟩ := by simp only [label, Fin.cases_succ, hc]
      rw [← cast_label hl w]
      simp only [position, componentPosition, Fin.cases_succ, dif_pos h]
      let w' := cast (congrArg (fun q : Symbol (System A) => q.2.val.Vertex) hl) w
      let b := vertex (ordinaryPiece C i) w'
      change (relabel (Lax369799.SystemEvaluation.fillLetter a) C.system).graph.label b.val =
        ⟨(C.system.graph.label b.val).1, (ordinaryLetter C b).val⟩
      change (⟨(C.system.graph.label b.val).1,
        Lax369799.SystemEvaluation.fillLetter a _ (C.system.graph.label b.val).2⟩ : Symbol A) = _
      exact congrArg (fun x => (⟨(C.system.graph.label b.val).1,
        Lax369799.SystemEvaluation.fillLetter a _ x⟩ : Symbol A)) (ordinaryLetter C b).property
    · have hc : continuation C i = none := by unfold continuation; rw [dif_neg h]
      have hl : label (atomicSystem a) (continuation C) i.succ = ⟨k, atomicSystem a⟩ := by
        simp only [label, Fin.cases_succ, hc]
      rw [← cast_label hl w]
      simp only [position, componentPosition, Fin.cases_succ, dif_neg h]
      exact hole_label C a

private theorem cast_initial {A : RankedSet} {b c : Symbol (System A)} (h : b = c)
    (w : b.2.val.Vertex) :
    c.2.val.graph.initial (cast (congrArg (fun q : Symbol (System A) => q.2.val.Vertex) h) w) ↔
      b.2.val.graph.initial w := by
  cases h
  rfl

theorem cast_internal {A : RankedSet} {b c : Symbol (System A)} (h : b = c)
    (w u : b.2.val.Vertex) (d : ℕ) :
    c.2.val.graph.edge (cast (congrArg (fun q : Symbol (System A) => q.2.val.Vertex) h) w) d
      (.inl (cast (congrArg (fun q : Symbol (System A) => q.2.val.Vertex) h) u)) ↔
      b.2.val.graph.edge w d (.inl u) := by
  cases h
  rfl

private theorem component_internal {A : RankedSet} {k : ℕ} (C : SetContext A k 0)
    (a : A k) (j : Fin (k + 2))
    (w u : (label (atomicSystem a) (continuation C) j).2.val.Vertex) (d : ℕ)
    (ht : (label (atomicSystem a) (continuation C) j).2.val.graph.edge w d (.inl u)) :
    C.system.graph.edge (componentPosition C a j w) d (.inl (componentPosition C a j u)) := by
  classical
  induction j using Fin.cases with
  | zero => obtain ⟨i, hi, he⟩ := ht; cases he
  | succ i =>
    by_cases h : (trim (ordinaryPiece C i)).Deterministic
    · have hc : continuation C i = some ⟨trim (ordinaryPiece C i), h⟩ := by
        unfold continuation; rw [dif_pos h]
      have hl : label (atomicSystem a) (continuation C) i.succ =
          ⟨1, ⟨trim (ordinaryPiece C i), h⟩⟩ := by simp only [label, Fin.cases_succ, hc]
      have hh := (cast_internal hl w u d).mpr ht
      simp only [componentPosition, Fin.cases_succ, dif_pos h]
      exact hh
    · have hc : continuation C i = none := by unfold continuation; rw [dif_neg h]
      have hl : label (atomicSystem a) (continuation C) i.succ = ⟨k, atomicSystem a⟩ := by
        simp only [label, Fin.cases_succ, hc]
      obtain ⟨j, hj, he⟩ := (cast_internal hl w u d).mpr ht
      cases he

private def EntryOrDirection {A : RankedSet} {k : ℕ} (C : SetContext A k 0)
    (i : Fin (k + 1)) (v : C.system.Vertex) : Prop :=
  (i = 0 ∧ C.system.graph.initial v) ∨
    ∃ d : Fin k, i = d.succ ∧ C.system.graph.edge (holeVertex C) d.val (.inl v)

private theorem slot_initial {A : RankedSet} {k : ℕ} (C : SetContext A k 0)
    (hC : C.system.Deterministic) (a : A k) (i : Fin (k + 1))
    (w : (label (atomicSystem a) (continuation C) i.succ).2.val.Vertex)
    (hi : (label (atomicSystem a) (continuation C) i.succ).2.val.graph.initial w) :
    EntryOrDirection C i (componentPosition C a i.succ w) := by
  classical
  by_cases h : (trim (ordinaryPiece C i)).Deterministic
  · have hc : continuation C i = some ⟨trim (ordinaryPiece C i), h⟩ := by
      unfold continuation; rw [dif_pos h]
    have hl : label (atomicSystem a) (continuation C) i.succ =
        ⟨1, ⟨trim (ordinaryPiece C i), h⟩⟩ := by simp only [label, Fin.cases_succ, hc]
    have hh := (cast_initial hl w).mpr hi
    simp only [componentPosition, Fin.cases_succ, dif_pos h]
    exact hh
  · have hc : continuation C i = none := by unfold continuation; rw [dif_neg h]
    simp only [componentPosition, Fin.cases_succ, dif_neg h]
    induction i using Fin.cases with
    | zero => exact Or.inl ⟨rfl, (DeterministicPieces.continuation_boundary C hC).1.mp hc⟩
    | succ d => exact Or.inr ⟨d, rfl, (DeterministicPieces.continuation_boundary C hC).2 d |>.mp hc⟩

theorem cast_exit {A : RankedSet} {b c : Symbol (System A)} (h : b = c)
    (w : b.2.val.Vertex) (i : Fin b.1) (d : ℕ) :
    c.2.val.graph.edge (cast (congrArg (fun q : Symbol (System A) => q.2.val.Vertex) h) w) d
      (.inr (cast (congrArg (fun q : Symbol (System A) => Fin q.1) h) i)) ↔
      b.2.val.graph.edge w d (.inr i) := by
  cases h
  rfl

private theorem hole_successor {A : RankedSet} {k : ℕ} (C : SetContext A k 0)
    (hC : C.system.Deterministic) (a : A k) (d : Fin k)
    (j : Fin (k + 2)) (hj : j = d.succ.succ)
    (u : (label (atomicSystem a) (continuation C) j).2.val.Vertex)
    (hu : (label (atomicSystem a) (continuation C) j).2.val.graph.initial u) :
    C.system.graph.edge (holeVertex C) d.val (.inl (componentPosition C a j u)) := by
  subst j
  have h := slot_initial C hC a d.succ u hu
  rcases h with ⟨he, _⟩ | ⟨e, he, hh⟩
  · exact False.elim (Fin.succ_ne_zero d he)
  · have he : d = e := Fin.succ_inj.mp he
    subst e
    exact hh

theorem cast_variable_value {A : RankedSet} {b c : Symbol (System A)} (h : b = c)
    (i : Fin b.1) : (cast (congrArg (fun q : Symbol (System A) => Fin q.1) h) i).val = i.val := by
  cases h
  rfl

private theorem component_exit {A : RankedSet} {k : ℕ} (C : SetContext A k 0)
    (hC : C.system.Deterministic) (a : A k) (j : Fin (k + 2))
    (w : (label (atomicSystem a) (continuation C) j).2.val.Vertex) (d : ℕ)
    (i : Fin (label (atomicSystem a) (continuation C) j).1)
    (hi : (label (atomicSystem a) (continuation C) j).2.val.graph.edge w d (.inr i))
    (t : Fin (k + 2)) (ht : (graph (atomicSystem a) (continuation C)).edge j i.val (.inl t))
    (u : (label (atomicSystem a) (continuation C) t).2.val.Vertex)
    (hu : (label (atomicSystem a) (continuation C) t).2.val.graph.initial u) :
    C.system.graph.edge (componentPosition C a j w) d (.inl (componentPosition C a t u)) := by
  classical
  obtain ⟨hd, heq⟩ := ht
  have ht : t = next (atomicSystem a) (continuation C) j i.val := Sum.inl.inj heq
  induction j using Fin.cases with
  | zero =>
    obtain ⟨e, he, hie⟩ := hi
    have hie : i = e := Sum.inr.inj hie
    subst e
    subst d
    apply hole_successor C hC a i t ?_ u hu
    rw [ht]
    have hi0 : i.val < k := i.isLt
    simp only [next, Fin.cases_zero, holeNext, dif_pos hi0]
    rfl
  | succ r =>
    by_cases h : (trim (ordinaryPiece C r)).Deterministic
    · have hc : continuation C r = some ⟨trim (ordinaryPiece C r), h⟩ := by
        unfold continuation; rw [dif_pos h]
      have hl : label (atomicSystem a) (continuation C) r.succ =
          ⟨1, ⟨trim (ordinaryPiece C r), h⟩⟩ := by simp only [label, Fin.cases_succ, hc]
      have hh := (cast_exit hl w i d).mpr hi
      have ht0 : t = 0 := by simpa only [next, Fin.cases_succ, hc, Option.elim_some] using ht
      clear ht heq
      subst t
      simp only [componentPosition, Fin.cases_succ, dif_pos h, Fin.cases_zero]
      exact hh
    · have hc : continuation C r = none := by unfold continuation; rw [dif_neg h]
      have hl : label (atomicSystem a) (continuation C) r.succ = ⟨k, atomicSystem a⟩ := by
        simp only [label, Fin.cases_succ, hc]
      let i' : Fin k := cast (congrArg (fun q : Symbol (System A) => Fin q.1) hl) i
      have hi' := (cast_exit hl w i d).mpr hi
      obtain ⟨e, he, hie⟩ := hi'
      have hie : i' = e := Sum.inr.inj hie
      subst e
      subst d
      simp only [componentPosition, Fin.cases_succ, dif_neg h]
      apply hole_successor C hC a i' t ?_ u hu
      rw [ht]
      simp only [next, Fin.cases_succ, hc, Option.elim_none]
      have hv : i.val = i'.val := (cast_variable_value hl i).symm
      rw [hv]
      simp only [holeNext, dif_pos i'.isLt]
      rfl

noncomputable def reconstruction {A : RankedSet} {k : ℕ} (C : SetContext A k 0)
    (hC : C.system.Deterministic) (a : A k) :
    Map (rawFlatten (graph (atomicSystem a) (continuation C)))
      (relabel (Lax369799.SystemEvaluation.fillLetter a) C.system).graph where
  toFun := position C a
  label := position_label C a
  initial := by
    rintro ⟨j, w⟩ hj
    have he : j = (0 : Fin (k + 1)).succ := hj.1
    subst j
    have hh := slot_initial C hC a 0 w hj.2
    rcases hh with ⟨_, hh⟩ | ⟨d, he, _⟩
    · exact hh
    · exact False.elim (Fin.succ_ne_zero d he.symm)
  root := by
    intro v hv
    rcases hv with hv | ⟨hv, _⟩
    · change v.2 ∈ (label (atomicSystem a) (continuation C) v.1).2.val.graph.root at hv
      rw [(label (atomicSystem a) (continuation C) v.1).2.property.2.1] at hv
      exact False.elim hv
    · exact False.elim hv
  edge := by
    intro v d t ht
    rcases ht with ⟨w, hw, rfl⟩ | ⟨i, hi, ht⟩
    · exact component_internal C a v.1 v.2 w d hw
    · rcases ht with ⟨w, hw, hw', rfl⟩ | ⟨j, _, _⟩
      · exact component_exit C hC a v.1 v.2 d i hi w.1 hw w.2 hw'
      · exact Fin.elim0 j

def compose {A : RankedSet} {n : ℕ} {V W X : Type}
    {G : Presentation A n V} {H : Presentation A n W} {I : Presentation A n X}
    (f : Map G H) (g : Map H I) : Map G I where
  toFun := g.toFun ∘ f.toFun
  label := fun v => (g.label _).trans (f.label v)
  initial := fun v h => g.initial _ (f.initial v h)
  root := fun v h => g.root _ (f.root v h)
  edge := by
    intro v d t ht
    have h := g.edge _ d _ (f.edge v d t ht)
    cases t <;> exact h

private theorem atomic_normal_form {A : RankedSet} (E : Lax369799.Algebras.Algebra A)
    (hE : Lax369799.Algebras.UnfoldInvariant E) {k : ℕ} (C : SetContext A k 0)
    (hC : C.system.Deterministic) (a : A k) :
    E.eval 0 (relabelSystem (Lax369799.SystemEvaluation.fillLetter a) ⟨C.system, hC⟩) =
      E.eval 0 (relabelSystem E.eval (pattern (atomicSystem a) (continuation C))) := by
  let T := pattern (atomicSystem a) (continuation C)
  let D := relabelSystem (Lax369799.SystemEvaluation.fillLetter a) ⟨C.system, hC⟩
  obtain ⟨U, hU⟩ := Flattening.flatten_system T
  have f : Morphism U.val D.val := by
    rw [hU]
    exact project (compose (flattenEmbedding (graph (atomicSystem a) (continuation C)))
      (reconstruction C hC a))
  have he := hE 0 D U ⟨U.val,
    ⟨f, MorphismTheorems.system_morphism_locally_surjective U D f⟩,
    ⟨MorphismTheorems.identity U.val, MorphismTheorems.identity_surjective U.val⟩⟩
  exact he.trans (E.associative 0 T U hU).symm

private theorem label_map {A B : RankedSet} (η : RankedMap A B) {k : ℕ}
    (a : A k) (P : Fin (k + 1) → Option (A 1)) (v : Fin (k + 2)) :
    label (η k a) (fun i => (P i).map (η 1)) v =
      ⟨(label a P v).1, η (label a P v).1 (label a P v).2⟩ := by
  induction v using Fin.cases with
  | zero => rfl
  | succ i =>
    dsimp only [label, Fin.cases_succ]
    generalize P i = o
    cases o <;> rfl

theorem next_map {A B : RankedSet} (η : RankedMap A B) {k : ℕ}
    (a : A k) (P : Fin (k + 1) → Option (A 1)) (v : Fin (k + 2)) (d : ℕ) :
    next (η k a) (fun i => (P i).map (η 1)) v d = next a P v d := by
  induction v using Fin.cases with
  | zero => rfl
  | succ i => cases h : P i <;> simp only [next, Fin.cases_succ, h, Option.map_none,
      Option.map_some, Option.elim_none, Option.elim_some]

private noncomputable def relabelMap {A B : RankedSet} (η : RankedMap A B) {k : ℕ}
    (a : A k) (P : Fin (k + 1) → Option (A 1)) :
    Map (relabel η (pattern a P).val).graph
      (graph (η k a) (fun i => (P i).map (η 1))) where
  toFun := vertex (graph a P)
  label := fun v => label_map η a P _
  initial := fun _ h => h
  root := fun _ h => h
  edge := by
    intro v d t ht
    obtain ⟨hd, he⟩ := ht
    refine ⟨?_, ?_⟩
    · rw [label_map]
      exact hd
    · change Sum.map (vertex (graph a P)) id t =
        .inl (next (η k a) (fun i => (P i).map (η 1)) (vertex (graph a P) (by exact v)) d)
      rw [next_map]
      exact he

theorem pattern_relabel {A B : RankedSet} (E : Lax369799.Algebras.Algebra B)
    (hE : Lax369799.Algebras.UnfoldInvariant E) (η : RankedMap A B) {k : ℕ}
    (a : A k) (P : Fin (k + 1) → Option (A 1)) :
    E.eval 0 (relabelSystem η (pattern a P)) =
      E.eval 0 (pattern (η k a) (fun i => (P i).map (η 1))) := by
  let S := relabelSystem η (pattern a P)
  let T := pattern (η k a) (fun i => (P i).map (η 1))
  let f : Morphism S.val T.val := lift (relabelMap η a P)
  exact hE 0 S T ⟨S.val,
    ⟨MorphismTheorems.identity S.val, MorphismTheorems.identity_surjective S.val⟩,
    ⟨f, MorphismTheorems.system_morphism_locally_surjective S T f⟩⟩

theorem evaluated_normal_form {A : RankedSet} (E : Lax369799.Algebras.Algebra A)
    (hE : Lax369799.Algebras.UnfoldInvariant E) {k : ℕ} (C : SetContext A k 0)
    (hC : C.system.Deterministic) (a : A k) :
    E.eval 0 (relabelSystem (Lax369799.SystemEvaluation.fillLetter a) ⟨C.system, hC⟩) =
      E.eval 0 (pattern a (fun i => (continuation C i).map (E.eval 1))) := by
  rw [atomic_normal_form E hE C hC a, pattern_relabel E hE E.eval, E.unit]

/--
---
conclusion: Lax369799.DeterministicNormalForms.pattern_exists
---
The entry vertex is unique, roots are absent, and the successor function
provides exactly one edge in each direction. Trimming preserves these properties.
-/
theorem pattern_exists {A : RankedSet} {k : ℕ} (a : A k)
    (P : Fin (k + 1) → Option (A 1)) :
    ∃ T : System A 0, T.val = trim (graph a P) := ⟨pattern a P, rfl⟩

/--
---
conclusion: Lax369799.DeterministicNormalForms.normal_form
---
Evaluate the substituted system first. Reconstruct the deterministic context
from its unary pieces, representing an absent piece by a copy of the hole.
The reconstruction covers the filled context, and associativity evaluates
its pieces. Relabelling then gives the pattern of optional unary values.
-/
theorem normal_form {A : RankedSet} (E : Lax369799.Algebras.Algebra A)
    (hE : Lax369799.Algebras.UnfoldInvariant E) {k : ℕ} (C : SetContext A k 0)
    (hC : C.system.Deterministic) (S : System A k) :
    ∃ U V : System A 0,
      U.val = plug C S.val ∧
      V.val = trim (graph (E.eval k S) (fun i => (continuation C i).map (E.eval 1))) ∧
      E.eval 0 U = E.eval 0 V := by
  obtain ⟨U, hU, he⟩ := SystemEvaluation.context_evaluation E C hC S
  exact ⟨U, pattern (E.eval k S) (fun i => (continuation C i).map (E.eval 1)), hU, rfl,
    he.trans (evaluated_normal_form E hE C hC (E.eval k S))⟩

end Lax369799Proofs.DeterministicNormalForms
