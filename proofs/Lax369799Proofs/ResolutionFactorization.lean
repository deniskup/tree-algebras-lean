import Lax369799Proofs.Flattening
import Lax369799Proofs.Renaming
import Mathlib.Data.Fintype.Sigma

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

namespace Lax369799Proofs.ResolutionFactorization
open Lax369799.RankedSystems Lax369799.Morphisms Lax369799.Flattening Lax369799.Resolutions
open Lax369799Proofs.Pullbacks

noncomputable def position {A : RankedSet} {n : ℕ} (S : SetSystem (SetSystem A) n)
    (R : System A n) (f : Morphism R.val (flatten S)) (r : R.val.Vertex) :=
  vertex (Lax369799Proofs.Flattening.graph S) (f.toFun r)

private theorem position_label {A : RankedSet} {n : ℕ} (S : SetSystem (SetSystem A) n)
    (R : System A n) (f : Morphism R.val (flatten S)) (r : R.val.Vertex) :
    (Inner S (position S R f r).1).graph.label (position S R f r).2 = R.val.graph.label r :=
  f.label r

private theorem position_edge {A : RankedSet} {n : ℕ} (S : SetSystem (SetSystem A) n)
    (R : System A n) (f : Morphism R.val (flatten S)) {r : R.val.Vertex} {d : ℕ}
    {t : R.val.Vertex ⊕ Fin n} (ht : R.val.graph.edge r d t) :
    (Lax369799Proofs.Flattening.graph S).edge (position S R f r) d (Sum.map (position S R f) id t) := by
  have h := f.edge r d t ht
  cases t <;> exact h

private def castInner {A : RankedSet} {n : ℕ} (S : SetSystem (SetSystem A) n)
    {s t : S.Vertex} (h : s = t) (v : (Inner S s).Vertex) : (Inner S t).Vertex := h ▸ v

private theorem cast_label {A : RankedSet} {n : ℕ} (S : SetSystem (SetSystem A) n)
    {s t : S.Vertex} (h : s = t) (v : (Inner S s).Vertex) :
    (Inner S t).graph.label (castInner S h v) = (Inner S s).graph.label v := by
  cases h
  rfl

private theorem cast_snd {A : RankedSet} {n : ℕ} (S : SetSystem (SetSystem A) n)
    {a : (s : S.Vertex) × (Inner S s).Vertex} {s : S.Vertex} (v : (Inner S s).Vertex)
    (h : a = ⟨s, v⟩) : castInner S (congrArg Sigma.fst h) a.2 = v := by
  cases h
  rfl

abbrev Fiber {A : RankedSet} {n : ℕ} (S : SetSystem (SetSystem A) n)
    (R : System A n) (f : Morphism R.val (flatten S)) (s : S.Vertex) :=
  {r : R.val.Vertex // (position S R f r).1 = s}

noncomputable def inner {A : RankedSet} {n : ℕ} (S : SetSystem (SetSystem A) n)
    (R : System A n) (f : Morphism R.val (flatten S)) {s : S.Vertex} (r : Fiber S R f s) :
    (Inner S s).Vertex := castInner S r.property (position S R f r.val).2

private theorem inner_label {A : RankedSet} {n : ℕ} (S : SetSystem (SetSystem A) n)
    (R : System A n) (f : Morphism R.val (flatten S)) {s : S.Vertex} (r : Fiber S R f s) :
    (Inner S s).graph.label (inner S R f r) = R.val.graph.label r.val :=
  (cast_label S r.property _).trans (position_label S R f r.val)

def CutAllowed {A : RankedSet} {n : ℕ} (S : SetSystem (SetSystem A) n)
    (R : System A n) (f : Morphism R.val (flatten S)) (s : S.Vertex)
    (p : Fin (S.graph.label s).1 × (R.val.Vertex ⊕ Fin n)) : Prop :=
  match p.2 with
  | .inl r => S.graph.edge s p.1.val (.inl (position S R f r).1) ∧
      (Inner S (position S R f r).1).graph.initial (position S R f r).2
  | .inr j => S.graph.edge s p.1.val (.inr j)

abbrev Cut {A : RankedSet} {n : ℕ} (S : SetSystem (SetSystem A) n)
    (R : System A n) (f : Morphism R.val (flatten S)) (s : S.Vertex) :=
  {p : Fin (S.graph.label s).1 × (R.val.Vertex ⊕ Fin n) // CutAllowed S R f s p}

def LocalEdge {A : RankedSet} {n : ℕ} (S : SetSystem (SetSystem A) n)
    (R : System A n) (f : Morphism R.val (flatten S)) {s : S.Vertex}
    (r : Fiber S R f s) (d : ℕ) (t : Fiber S R f s ⊕ Cut S R f s) : Prop :=
  match t with
  | .inl w => R.val.graph.edge r.val d (.inl w.val) ∧
      (Inner S s).graph.edge (inner S R f r) d (.inl (inner S R f w))
  | .inr c => R.val.graph.edge r.val d c.val.2 ∧
      (Inner S s).graph.edge (inner S R f r) d (.inr c.val.1)

private theorem local_total {A : RankedSet} {n : ℕ} (S : SetSystem (SetSystem A) n)
    (R : System A n) (f : Morphism R.val (flatten S)) {s : S.Vertex}
    (r : Fiber S R f s) (d : ℕ) (hd : d < (R.val.graph.label r.val).1) :
    ∃ t, LocalEdge S R f r d t := by
  obtain ⟨t, ht, _⟩ := R.property.2.2 r.val d hd
  have hf := position_edge S R f ht
  rcases r with ⟨r, hr⟩
  subst s
  rcases hf with ⟨w, hw, he⟩ | ⟨i, hi, hf⟩
  · cases t with
    | inr j => cases he
    | inl q =>
      have hp : position S R f q = ⟨(position S R f r).1, w⟩ := Sum.inl.inj he
      have hc := congrArg Sigma.fst hp
      refine ⟨.inl ⟨q, hc⟩, ht, ?_⟩
      change (Inner S (position S R f r).1).graph.edge (position S R f r).2 d
        (.inl (castInner S hc (position S R f q).2))
      rw [cast_snd S w hp]
      exact hw
  · rcases hf with ⟨w, hw, hw', he⟩ | ⟨j, hj, he⟩
    · cases t with
      | inr j => cases he
      | inl q =>
        have hp : position S R f q = w := Sum.inl.inj he
        subst w
        exact ⟨.inr ⟨(i, .inl q), hw, hw'⟩, ht, hi⟩
    · cases t with
      | inl q => cases he
      | inr l =>
        have he := Sum.inr.inj he
        subst j
        exact ⟨.inr ⟨(i, .inr l), hj⟩, ht, hi⟩

noncomputable instance fiberFintype {A : RankedSet} {n : ℕ} (S : SetSystem (SetSystem A) n)
    (R : System A n) (f : Morphism R.val (flatten S)) (s : S.Vertex) : Fintype (Fiber S R f s) := by
  classical
  unfold Fiber
  infer_instance

noncomputable instance cutFintype {A : RankedSet} {n : ℕ} (S : SetSystem (SetSystem A) n)
    (R : System A n) (f : Morphism R.val (flatten S)) (s : S.Vertex) : Fintype (Cut S R f s) := by
  classical
  unfold Cut
  infer_instance

noncomputable def nextLocal {A : RankedSet} {n : ℕ} (S : SetSystem (SetSystem A) n)
    (R : System A n) (f : Morphism R.val (flatten S)) {s : S.Vertex}
    (r : Fiber S R f s) (d : Fin (R.val.graph.label r.val).1) : Fiber S R f s ⊕ Cut S R f s :=
  Classical.choose (local_total S R f r d.val d.isLt)

private theorem nextLocal_spec {A : RankedSet} {n : ℕ} (S : SetSystem (SetSystem A) n)
    (R : System A n) (f : Morphism R.val (flatten S)) {s : S.Vertex}
    (r : Fiber S R f s) (d : Fin (R.val.graph.label r.val).1) :
    LocalEdge S R f r d.val (nextLocal S R f r d) :=
  Classical.choose_spec (local_total S R f r d.val d.isLt)

noncomputable def cutIndex {A : RankedSet} {n : ℕ} (S : SetSystem (SetSystem A) n)
    (R : System A n) (f : Morphism R.val (flatten S)) (s : S.Vertex) := by
  classical
  exact Fintype.equivFin (Cut S R f s)

noncomputable def cutMap {A : RankedSet} {n : ℕ} (S : SetSystem (SetSystem A) n)
    (R : System A n) (f : Morphism R.val (flatten S)) (s : S.Vertex) :
    Fin (Fintype.card (Cut S R f s)) → Fin (S.graph.label s).1 :=
  fun i => ((cutIndex S R f s).symm i).val.1

noncomputable def localGraph {A : RankedSet} {n : ℕ} (S : SetSystem (SetSystem A) n)
    (R : System A n) (f : Morphism R.val (flatten S)) {s : S.Vertex} (entry : Fiber S R f s) :
    Presentation A (Fintype.card (Cut S R f s)) (Fiber S R f s) where
  label := fun r => R.val.graph.label r.val
  initial := {entry}
  root := ∅
  edge := fun r d t => ∃ hd : d < (R.val.graph.label r.val).1,
    t = Sum.map id (cutIndex S R f s) (nextLocal S R f r ⟨d, hd⟩)
  direction_valid := fun _ _ _ h => h.choose

private theorem localGraph_total {A : RankedSet} {n : ℕ} (S : SetSystem (SetSystem A) n)
    (R : System A n) (f : Morphism R.val (flatten S)) {s : S.Vertex} (entry : Fiber S R f s)
    (r : Fiber S R f s) (d : ℕ) (hd : d < ((localGraph S R f entry).label r).1) :
    ∃! t, (localGraph S R f entry).edge r d t := by
  refine ⟨Sum.map id (cutIndex S R f s) (nextLocal S R f r ⟨d, hd⟩), ⟨hd, rfl⟩, ?_⟩
  rintro t ⟨h, rfl⟩
  rfl

noncomputable def localSystem {A : RankedSet} {n : ℕ} (S : SetSystem (SetSystem A) n)
    (R : System A n) (f : Morphism R.val (flatten S)) {s : S.Vertex} (entry : Fiber S R f s) :
    System A (Fintype.card (Cut S R f s)) := by
  classical
  exact ⟨trim (localGraph S R f entry),
    Yields.trim_deterministic _ entry rfl rfl (localGraph_total S R f entry)⟩

private theorem local_edge_morphism {A : RankedSet} {n : ℕ} (S : SetSystem (SetSystem A) n)
    (R : System A n) (f : Morphism R.val (flatten S)) {s : S.Vertex} (entry : Fiber S R f s)
    (r : Fiber S R f s) (d : ℕ) (t : Fiber S R f s ⊕ Fin (Fintype.card (Cut S R f s)))
    (ht : (localGraph S R f entry).edge r d t) :
    (Inner S s).graph.edge (inner S R f r) d (Sum.map (inner S R f) (cutMap S R f s) t) := by
  obtain ⟨hd, rfl⟩ := ht
  have h := nextLocal_spec S R f r ⟨d, hd⟩
  cases he : nextLocal S R f r ⟨d, hd⟩ with
  | inl w =>
    rw [he] at h
    exact h.2
  | inr c =>
    rw [he] at h
    simpa only [Sum.map_inr, cutMap, Equiv.symm_apply_apply] using h.2

noncomputable def localMorphism {A : RankedSet} {n : ℕ} (S : SetSystem (SetSystem A) n)
    (R : System A n) (f : Morphism R.val (flatten S)) {s : S.Vertex} (entry : Fiber S R f s)
    (he : (Inner S s).graph.initial (inner S R f entry)) :
    Morphism (rename (cutMap S R f s) (localSystem S R f entry).val) (Inner S s) where
  toFun := by
    intro v
    change (trim (localGraph S R f entry)).Vertex at v
    exact inner S R f (vertex (localGraph S R f entry) v)
  label := fun _ => inner_label S R f _
  initial := by
    intro v hv
    change (trim (localGraph S R f entry)).Vertex at v
    change vertex (localGraph S R f entry) v = entry at hv
    change (Inner S s).graph.initial (inner S R f (vertex (localGraph S R f entry) v))
    rw [hv]
    exact he
  root := fun _ h => False.elim h
  edge := by
    rintro v d t ⟨u, hu, rfl⟩
    change (trim (localGraph S R f entry)).Vertex at v
    change (trim (localGraph S R f entry)).Vertex ⊕ Fin (Fintype.card (Cut S R f s)) at u
    have hh := local_edge_morphism S R f entry (vertex (localGraph S R f entry) v) d
      (Sum.map (vertex (localGraph S R f entry)) id u) hu
    cases u <;> exact hh

abbrev Entry {A : RankedSet} {n : ℕ} (S : SetSystem (SetSystem A) n)
    (R : System A n) (f : Morphism R.val (flatten S)) :=
  {r : R.val.Vertex // (Inner S (position S R f r).1).graph.initial (position S R f r).2}

noncomputable instance entryFintype {A : RankedSet} {n : ℕ} (S : SetSystem (SetSystem A) n)
    (R : System A n) (f : Morphism R.val (flatten S)) : Fintype (Entry S R f) := by
  classical
  unfold Entry
  infer_instance

noncomputable def entryInitial {A : RankedSet} {n : ℕ} (S : SetSystem (SetSystem A) n)
    (R : System A n) (f : Morphism R.val (flatten S)) : Entry S R f := by
  let r := Classical.choose R.property.1
  have hr : r ∈ R.val.graph.initial := by rw [Classical.choose_spec R.property.1]; rfl
  exact ⟨r, (f.initial r hr).2⟩

noncomputable def cutTarget {A : RankedSet} {n : ℕ} (S : SetSystem (SetSystem A) n)
    (R : System A n) (f : Morphism R.val (flatten S)) {s : S.Vertex} :
    Cut S R f s → Entry S R f ⊕ Fin n
  | ⟨(_, .inl r), h⟩ => .inl ⟨r, h.2⟩
  | ⟨(_, .inr j), _⟩ => .inr j

private theorem cutTarget_forget {A : RankedSet} {n : ℕ} (S : SetSystem (SetSystem A) n)
    (R : System A n) (f : Morphism R.val (flatten S)) {s : S.Vertex} (c : Cut S R f s) :
    Sum.map Subtype.val id (cutTarget S R f c) = c.val.2 := by
  obtain ⟨⟨i, t⟩, h⟩ := c
  cases t <;> rfl

private theorem cutTarget_edge {A : RankedSet} {n : ℕ} (S : SetSystem (SetSystem A) n)
    (R : System A n) (f : Morphism R.val (flatten S)) {s : S.Vertex} (c : Cut S R f s) :
    S.graph.edge s c.val.1.val
      (Sum.map (fun r : Entry S R f => (position S R f r.val).1) id (cutTarget S R f c)) := by
  obtain ⟨⟨i, t⟩, h⟩ := c
  cases t with
  | inl r => exact h.1
  | inr j => exact h

noncomputable def outerGraph {A : RankedSet} {n : ℕ} (S : SetSystem (SetSystem A) n)
    (R : System A n) (f : Morphism R.val (flatten S)) : Presentation (System A) n (Entry S R f) where
  label := fun r => ⟨Fintype.card (Cut S R f (position S R f r.val).1),
    localSystem S R f ⟨r.val, rfl⟩⟩
  initial := {entryInitial S R f}
  root := ∅
  edge := fun r d t => ∃ hd : d < Fintype.card (Cut S R f (position S R f r.val).1),
    t = cutTarget S R f ((cutIndex S R f (position S R f r.val).1).symm ⟨d, hd⟩)
  direction_valid := fun _ _ _ h => h.choose

private theorem outerGraph_total {A : RankedSet} {n : ℕ} (S : SetSystem (SetSystem A) n)
    (R : System A n) (f : Morphism R.val (flatten S)) (r : Entry S R f) (d : ℕ)
    (hd : d < ((outerGraph S R f).label r).1) : ∃! t, (outerGraph S R f).edge r d t := by
  refine ⟨cutTarget S R f ((cutIndex S R f (position S R f r.val).1).symm ⟨d, hd⟩), ⟨hd, rfl⟩, ?_⟩
  rintro t ⟨h, rfl⟩
  rfl

noncomputable def outerSystem {A : RankedSet} {n : ℕ} (S : SetSystem (SetSystem A) n)
    (R : System A n) (f : Morphism R.val (flatten S)) : System (System A) n :=
  ⟨trim (outerGraph S R f), Yields.trim_deterministic _ (entryInitial S R f) rfl rfl
    (outerGraph_total S R f)⟩

noncomputable def outerResolution {A : RankedSet} {n : ℕ} (S : SetSystem (SetSystem A) n)
    (R : System A n) (f : Morphism R.val (flatten S)) : FlattenResolution S (outerSystem S R f) where
  vertex := fun v => (position S R f (vertex (outerGraph S R f) v).val).1
  variableMap := fun v => cutMap S R f (position S R f (vertex (outerGraph S R f) v).val).1
  initial := by
    intro v hv
    change vertex (outerGraph S R f) v = entryInitial S R f at hv
    change S.graph.initial (position S R f (vertex (outerGraph S R f) v).val).1
    rw [hv]
    have hr : (entryInitial S R f).val ∈ R.val.graph.initial := by
      rw [Classical.choose_spec R.property.1]
      rfl
    exact (f.initial _ hr).1
  resolves := by
    intro v
    let r := vertex (outerGraph S R f) v
    exact ⟨localMorphism S R f ⟨r.val, rfl⟩ r.property⟩
  transition := by
    intro v i w h
    let r := vertex (outerGraph S R f) v
    let c := (cutIndex S R f (position S R f r.val).1).symm i
    obtain ⟨hd, he⟩ := h
    have hh := cutTarget_edge S R f c
    change Sum.inl (vertex (outerGraph S R f) w) = cutTarget S R f c at he
    rw [← he] at hh
    exact hh
  exit := by
    intro v i j h
    let r := vertex (outerGraph S R f) v
    let c := (cutIndex S R f (position S R f r.val).1).symm i
    obtain ⟨hd, he⟩ := h
    have hh := cutTarget_edge S R f c
    change Sum.inr j = cutTarget S R f c at he
    rw [← he] at hh
    exact hh

noncomputable def localTarget {A : RankedSet} {n : ℕ} (S : SetSystem (SetSystem A) n)
    (R : System A n) (f : Morphism R.val (flatten S)) {s : S.Vertex} :
    Fiber S R f s ⊕ Fin (Fintype.card (Cut S R f s)) → R.val.Vertex ⊕ Fin n
  | .inl w => .inl w.val
  | .inr i => ((cutIndex S R f s).symm i).val.2

private theorem local_step {A : RankedSet} {n : ℕ} (S : SetSystem (SetSystem A) n)
    (R : System A n) (f : Morphism R.val (flatten S)) {s : S.Vertex}
    (entry r : Fiber S R f s) (d : ℕ) (t)
    (ht : (localGraph S R f entry).edge r d t) :
    R.val.graph.edge r.val d (localTarget S R f t) := by
  obtain ⟨hd, rfl⟩ := ht
  have h := (nextLocal_spec S R f r ⟨d, hd⟩)
  cases he : nextLocal S R f r ⟨d, hd⟩ with
  | inl w => rw [he] at h; exact h.1
  | inr c =>
    rw [he] at h
    simpa only [Sum.map_inr, localTarget, Equiv.symm_apply_apply] using h.1

noncomputable def outerLabels {A : RankedSet} {n : ℕ} (S : SetSystem (SetSystem A) n)
    (R : System A n) (f : Morphism R.val (flatten S)) : SetSystem (SetSystem A) n :=
  relabel (fun _ (U : System A _) => U.val) (outerSystem S R f).val

noncomputable def flattenedPosition {A : RankedSet} {n : ℕ} (S : SetSystem (SetSystem A) n)
    (R : System A n) (f : Morphism R.val (flatten S))
    (v : (v : (outerLabels S R f).Vertex) × (Inner (outerLabels S R f) v).Vertex) :
    R.val.Vertex :=
  (vertex (localGraph S R f ⟨(vertex (outerGraph S R f) (by exact v.1)).val, rfl⟩) (by exact v.2)).val

private theorem flattened_initial {A : RankedSet} {n : ℕ} (S : SetSystem (SetSystem A) n)
    (R : System A n) (f : Morphism R.val (flatten S))
    (v : (v : (outerLabels S R f).Vertex) × (Inner (outerLabels S R f) v).Vertex)
    (hv : (Inner (outerLabels S R f) v.1).graph.initial v.2) :
    flattenedPosition S R f v = (vertex (outerGraph S R f) (by exact v.1)).val := by
  let r := vertex (outerGraph S R f) (by exact v.1)
  let entry : Fiber S R f (position S R f r.val).1 := ⟨r.val, rfl⟩
  have h : vertex (localGraph S R f entry) (by exact v.2) = entry := hv
  exact congrArg Subtype.val h

noncomputable def flattenedMap {A : RankedSet} {n : ℕ} (S : SetSystem (SetSystem A) n)
    (R : System A n) (f : Morphism R.val (flatten S)) :
    Map (Flattening.graph (outerLabels S R f)) R.val.graph where
  toFun := flattenedPosition S R f
  label := fun _ => rfl
  initial := by
    intro v hv
    rw [flattened_initial S R f v hv.2]
    have h := hv.1
    change vertex (outerGraph S R f) (by exact v.1) = entryInitial S R f at h
    rw [h, Classical.choose_spec R.property.1]
    rfl
  root := by
    intro v hv
    rcases hv with hv | ⟨hv, _⟩
    · exact False.elim hv
    · exact False.elim hv
  edge := by
    intro v d t ht
    let r := vertex (outerGraph S R f) (by exact v.1)
    let entry : Fiber S R f (position S R f r.val).1 := ⟨r.val, rfl⟩
    let x := vertex (localGraph S R f entry) (by exact v.2)
    rcases ht with ⟨w, hw, rfl⟩ | ⟨i, hi, ht⟩
    · exact local_step S R f entry x d
        (.inl (vertex (localGraph S R f entry) (by exact w))) (by exact hw)
    · have hs := local_step S R f entry x d (.inr (by exact i)) (by exact hi)
      let c := (cutIndex S R f (position S R f r.val).1).symm (by exact i)
      change R.val.graph.edge (flattenedPosition S R f v) d c.val.2 at hs
      rcases ht with ⟨w, hw, hw', rfl⟩ | ⟨j, hj, rfl⟩
      · obtain ⟨hd, he⟩ := hw
        change Sum.inl (vertex (outerGraph S R f) (by exact w.1)) = cutTarget S R f c at he
        have hh := cutTarget_forget S R f c
        rw [← he] at hh
        change Sum.inl (vertex (outerGraph S R f) (by exact w.1)).val = c.val.2 at hh
        change R.val.graph.edge (flattenedPosition S R f v) d (.inl (flattenedPosition S R f w))
        rw [flattened_initial S R f w hw', hh]
        exact hs
      · obtain ⟨hd, he⟩ := hj
        change Sum.inr j = cutTarget S R f c at he
        have hh := cutTarget_forget S R f c
        rw [← he] at hh
        change Sum.inr j = c.val.2 at hh
        change R.val.graph.edge (flattenedPosition S R f v) d (.inr j)
        rw [hh]
        exact hs

/--
---
conclusion: Lax369799.FlatteningTheorems.resolution_to_flatten_resolution
---
Choose an internal continuation or a variable exit for every resolution edge.
The resulting local deterministic resolutions form an outer deterministic
system. Its flattening maps to the given resolution and hence unfolds to it.
-/
theorem resolution_to_flatten_resolution {A : RankedSet} {n : ℕ}
    (S : SetSystem (SetSystem A) n) (R : System A n)
    (hR : DirectResolution (flatten S) R) :
    ∃ (T : System (System A) n) (U : System A n),
      Nonempty (FlattenResolution S T) ∧ SystemFlattening T U ∧ UnfoldsTo R.val U.val := by
  classical
  obtain ⟨f⟩ := hR
  obtain ⟨U, hU⟩ := Flattening.flatten_system (outerSystem S R f)
  have g : Morphism U.val R.val := by
    change U.val = flatten (outerLabels S R f) at hU
    rw [hU]
    exact project (flattenedMap S R f)
  exact ⟨outerSystem S R f, U, ⟨outerResolution S R f⟩, hU,
    ⟨g, MorphismTheorems.system_morphism_locally_surjective U R g⟩⟩

end Lax369799Proofs.ResolutionFactorization
