import Lax369799Proofs.DeltaContext
import Lax369799Proofs.NormalMonotonicity

set_option backward.isDefEq.respectTransparency false

namespace Lax369799Proofs.DeltaComparison
open Lax369799.RankedSystems Lax369799.Morphisms Lax369799.Flattening Lax369799.SetAlgebras
open Lax369799.ExtremalContexts Lax369799Proofs.Pullbacks
open Lax369799Proofs.AlgebraicDecomposition

private noncomputable def rawDelta {A : RankedSet} {k : ℕ}
    (x : Data A k) (a : A k) := Lax369799Proofs.Flattening.graph (deltaPattern x.1 x.2 a)

private theorem root_reachable {A : RankedSet} {k : ℕ} (x : Data A k) (a : A k) :
    (rawDelta x a).Reachable ⟨(0 : Fin (k + 1)), (0 : Fin 1)⟩ :=
  ⟨⟨(0 : Fin (k + 1)), (0 : Fin 1)⟩, Or.inr (Or.inr ⟨Or.inl rfl, True.intro⟩), .refl⟩

private theorem center_reachable {A : RankedSet} {k : ℕ}
    (x : Data A k) (a : A k) (i : Fin k) :
    (rawDelta x a).Reachable ⟨i.succ, (0 : Fin (k + 1))⟩ :=
  ⟨⟨i.succ, (0 : Fin (k + 1))⟩, Or.inl ⟨Fin.succ_ne_zero i, rfl⟩, .refl⟩

private theorem unary_reachable {A : RankedSet} {k : ℕ}
    (x : Data A k) (a : A k) (i j : Fin k) :
    (rawDelta x a).Reachable ⟨i.succ, j.succ⟩ :=
  ⟨⟨i.succ, (0 : Fin (k + 1))⟩, Or.inl ⟨Fin.succ_ne_zero i, rfl⟩,
    Relation.ReflTransGen.refl.tail ⟨j.val, Or.inl ⟨j.succ, Or.inl ⟨j, rfl, rfl⟩, rfl⟩⟩⟩

private noncomputable def rootVertex {A : RankedSet} {k : ℕ} (x : Data A k) (a : A k) :
    (delta x.1 x.2 a).Vertex := index (rawDelta x a) ⟨_, root_reachable x a⟩

private noncomputable def center {A : RankedSet} {k : ℕ} (x : Data A k) (a : A k) (i : Fin k) :
    (delta x.1 x.2 a).Vertex := index (rawDelta x a) ⟨_, center_reachable x a i⟩

private noncomputable def unary {A : RankedSet} {k : ℕ} (x : Data A k) (a : A k) (i j : Fin k) :
    (delta x.1 x.2 a).Vertex := index (rawDelta x a) ⟨_, unary_reachable x a i j⟩

private theorem center_initial {A : RankedSet} {k : ℕ} (x : Data A k) (a : A k) (i : Fin k) :
    center x a i ∈ (delta x.1 x.2 a).graph.initial := by
  change (rawDelta x a).initial (vertex (rawDelta x a) (index (rawDelta x a) _))
  rw [vertex_index]
  exact ⟨Fin.succ_ne_zero i, rfl⟩

private theorem root_root {A : RankedSet} {k : ℕ} (x : Data A k) (a : A k) :
    rootVertex x a ∈ (delta x.1 x.2 a).graph.root := by
  change (rawDelta x a).root (vertex (rawDelta x a) (index (rawDelta x a) _))
  rw [vertex_index]
  exact Or.inr ⟨Or.inl rfl, True.intro⟩

private theorem center_root {A : RankedSet} {k : ℕ} (x : Data A k) (a : A k) (i : Fin k)
    (h : x.1.root) : center x a i ∈ (delta x.1 x.2 a).graph.root := by
  change (rawDelta x a).root (vertex (rawDelta x a) (index (rawDelta x a) _))
  rw [vertex_index]
  exact Or.inr ⟨Or.inr h, rfl⟩

private theorem edge_root {A : RankedSet} {k : ℕ} (x : Data A k) (a : A k) (i : Fin k) :
    (delta x.1 x.2 a).graph.edge (rootVertex x a) 0 (.inl (center x a i)) := by
  change (rawDelta x a).edge (vertex (rawDelta x a) (index (rawDelta x a) _)) 0
    (.inl (vertex (rawDelta x a) (index (rawDelta x a) _)))
  simp only [vertex_index]
  exact Or.inr ⟨(0 : Fin 1), ⟨0, rfl, rfl⟩,
    Or.inl ⟨⟨i.succ, (0 : Fin (k + 1))⟩, ⟨rfl, ⟨i, rfl⟩⟩, rfl, rfl⟩⟩

private theorem edge_out {A : RankedSet} {k : ℕ} (x : Data A k) (a : A k) (i j : Fin k) :
    (delta x.1 x.2 a).graph.edge (center x a i) j.val (.inl (unary x a i j)) := by
  change (rawDelta x a).edge (vertex (rawDelta x a) (index (rawDelta x a) _)) j.val
    (.inl (vertex (rawDelta x a) (index (rawDelta x a) _)))
  simp only [vertex_index]
  exact Or.inl ⟨j.succ, Or.inl ⟨j, rfl, rfl⟩, rfl⟩

private theorem edge_back {A : RankedSet} {k : ℕ} (x : Data A k) (a : A k) (i j : Fin k) :
    (delta x.1 x.2 a).graph.edge (unary x a i j) 0 (.inl (center x a i)) := by
  change (rawDelta x a).edge (vertex (rawDelta x a) (index (rawDelta x a) _)) 0
    (.inl (vertex (rawDelta x a) (index (rawDelta x a) _)))
  simp only [vertex_index]
  exact Or.inl ⟨(0 : Fin (k + 1)), ⟨rfl, rfl⟩, rfl⟩

private theorem edge_loop {A : RankedSet} {k : ℕ} (x : Data A k) (a : A k) (i j : Fin k)
    (h : j ∈ x.1.loops) :
    (delta x.1 x.2 a).graph.edge (center x a i) j.val (.inl (center x a i)) := by
  change (rawDelta x a).edge (vertex (rawDelta x a) (index (rawDelta x a) _)) j.val
    (.inl (vertex (rawDelta x a) (index (rawDelta x a) _)))
  simp only [vertex_index]
  exact Or.inl ⟨(0 : Fin (k + 1)), Or.inr (Or.inl ⟨j, h, rfl, rfl⟩), rfl⟩

private theorem edge_exit {A : RankedSet} {k : ℕ} (x : Data A k) (a : A k) (i : Fin k) :
    (delta x.1 x.2 a).graph.edge (center x a i) i.val (.inr i) := by
  change (rawDelta x a).edge (vertex (rawDelta x a) (index (rawDelta x a) _)) i.val (.inr i)
  rw [vertex_index]
  exact Or.inr ⟨(0 : Fin 1), Or.inr (Or.inr ⟨rfl, rfl⟩), Or.inr ⟨i, ⟨rfl, rfl⟩, rfl⟩⟩

private noncomputable def testPattern {A : RankedSet} {k : ℕ}
    (x y : Data A k) (a : A k) :=
  relabel (substitution (delta x.1 x.2 a)) (normalContext y.1 y.2).system

private noncomputable def embedVertex {A : RankedSet} {k : ℕ}
    (x : Data A k) (a : A k) (i : Fin k) : Fin (k + 2) → (delta x.1 x.2 a).Vertex :=
  Fin.cases (center x a i) (Fin.cases (rootVertex x a) (unary x a i))

private noncomputable def testMapRaw {A : RankedSet} {k : ℕ}
    (x y : Data A k) (a : A k) (i : Fin k) (B : Boundary k)
    (hr : B.root → x.1.root ∨ y.1.root)
    (hl : ∀ j ∈ B.loops, j ∈ x.1.loops ∨ (j = i ∧ j ∈ y.1.loops)) :
    Map (relabel (letterSubstitution a) (normalContext B x.2).system).graph
      (Lax369799Proofs.Flattening.graph (testPattern x y a)) where
  toFun := fun v => ⟨(0 : Fin (k + 2)), embedVertex x a i v⟩
  label := by
    intro v
    cases v using Fin.cases with
    | zero =>
      change (rawDelta x a).label (vertex (rawDelta x a) (index (rawDelta x a) _)) = _
      rw [vertex_index]
      rfl
    | succ j =>
      cases j using Fin.cases <;>
        change (rawDelta x a).label (vertex (rawDelta x a) (index (rawDelta x a) _)) = _ <;>
        rw [vertex_index] <;> rfl
  initial := fun _ h => False.elim h
  root := by
    intro v h
    cases v using Fin.cases with
    | zero =>
      rcases h with h | ⟨_, h⟩
      · exact False.elim (Fin.succ_ne_zero (0 : Fin (k + 1)) h.symm)
      · rcases hr h with hx | hy
        · exact Or.inl (center_root x a i hx)
        · exact Or.inr ⟨Or.inr ⟨rfl, hy⟩, center_initial x a i⟩
    | succ j =>
      rcases h with h | ⟨h, _⟩
      · have hj : j = 0 := Fin.succ_inj.mp h
        subst j
        exact Or.inl (root_root x a)
      · exact False.elim (Fin.succ_ne_zero j h)
  edge := by
    intro v d t h
    cases t with
    | inr j => exact Fin.elim0 j
    | inl w =>
      cases v using Fin.cases with
      | zero =>
        rcases h with ⟨j, hd, he⟩ | ⟨j, hj, hd, he⟩
        · have he := Sum.inl.inj he
          subst w
          subst d
          exact Or.inl ⟨unary x a i j, edge_out x a i j, rfl⟩
        · have he := Sum.inl.inj he
          subst w
          subst d
          rcases hl j hj with hj | ⟨hji, hj⟩
          · exact Or.inl ⟨center x a i, edge_loop x a i j hj, rfl⟩
          · subst j
            exact Or.inr ⟨i, edge_exit x a i,
              Or.inl ⟨⟨(0 : Fin (k + 2)), center x a i⟩,
                Or.inr ⟨i, hj, rfl, rfl⟩, center_initial x a i, rfl⟩⟩
      | succ j =>
        obtain ⟨hd, he⟩ := h
        have he := Sum.inl.inj he
        subst w
        subst d
        cases j using Fin.cases with
        | zero => exact Or.inl ⟨center x a i, edge_root x a i, rfl⟩
        | succ j => exact Or.inl ⟨center x a i, edge_back x a i j, rfl⟩

private theorem test_bound {A : RankedSet} (E : SetAlgebra A) {k : ℕ}
    (x y : Data A k) (a : A k) (i : Fin k) (B : Boundary k)
    (hr : B.root → x.1.root ∨ y.1.root)
    (hl : ∀ j ∈ B.loops, j ∈ x.1.loops ∨ (j = i ∧ j ∈ y.1.loops)) :
    Below E (value E (E.eval k (delta x.1 x.2 a)) y) (value E a (B, x.2)) := by
  have hm := E.morphism 0
    (relabel (letterSubstitution a) (normalContext B x.2).system)
    (plug (normalContext y.1 y.2) (delta x.1 x.2 a)) ⟨lift (testMapRaw x y a i B hr hl)⟩
  rw [Evaluation.context_evaluation E (normalContext y.1 y.2) (delta x.1 x.2 a)] at hm
  obtain ⟨f, hf⟩ := plug_atomic_cover (normalContext B x.2) a
  rw [← SumEvaluation.eval_cover E f hf] at hm
  exact hm

/--
---
conclusion: Lax369799.ExtremalContexts.delta_boundary_comparison
---
An extra root mark in the testing context makes a component center a
root. A loop in direction i returns the exit of U_i to its own center.
The corresponding subsystem morphisms and boundary minimality force
both features to be present in the extremal context already.
-/
theorem delta_boundary_comparison {A : RankedSet} (E : SetAlgebra A) (f : A 0)
    {k : ℕ} (hk : 1 ≤ k) (x y : Data A k) (a : A k)
    (hx : IsExtremal E f a x) (hy : Accepts E f (E.eval k (delta x.1 x.2 a)) y) :
    (y.1.root → x.1.root) ∧ y.1.loops ⊆ x.1.loops := by
  have hrefl := (SetAlgebraTheorems.order_laws E 1).1
  have htrans := (SetAlgebraTheorems.order_laws E 0).2.2.1
  constructor
  · intro hyr
    let i : Fin k := ⟨0, by omega⟩
    let B : Boundary k := ⟨True, x.1.loops⟩
    have hz : DataBelow E (B, x.2) x := ⟨fun _ => True.intro, Set.Subset.rfl, fun j => hrefl _⟩
    have ha : Accepts E f a (B, x.2) := htrans _ _ _ hy
      (test_bound E x y a i B (fun _ => Or.inr hyr) (fun _ h => Or.inl h))
    exact (hx.2 (B, x.2) hz ha).1 True.intro
  · intro i hi
    let B : Boundary k := ⟨x.1.root, insert i x.1.loops⟩
    have hz : DataBelow E (B, x.2) x := ⟨id, Set.subset_insert i _, fun j => hrefl _⟩
    have ha : Accepts E f a (B, x.2) := htrans _ _ _ hy
      (test_bound E x y a i B Or.inl (by
        intro j hj
        rcases hj with rfl | hj
        · exact Or.inr ⟨rfl, hi⟩
        · exact Or.inl hj))
    exact (hx.2 (B, x.2) hz ha).2.1 (Or.inl rfl)

private def pairSystem {A : RankedSet} (b c : A 1) : SetSystem A 1 where
  size := 2
  graph := {
    label := fun v => ⟨1, if v = 0 then b else c⟩
    initial := Set.univ
    root := ∅
    edge := fun _ d t => d = 0 ∧ t = .inr 0
    direction_valid := by rintro v d t ⟨rfl, _⟩; exact Nat.zero_lt_one }
  reachable := fun v => ⟨v, Or.inl True.intro, .refl⟩

private theorem eval_pair {A : RankedSet} (E : SetAlgebra A) (b c : A 1) :
    E.eval 1 (pairSystem b c) = meet E b c := by
  let G := SumEvaluation.sumGraph (atomic b) (atomic c)
  let f : Map G (pairSystem b c).graph := {
    toFun := Sum.elim (fun _ => (0 : Fin 2)) (fun _ => (1 : Fin 2))
    label := by intro v; cases v <;> rfl
    initial := fun _ _ => True.intro
    root := by intro v h; cases v <;> exact False.elim h
    edge := by
      intro v d t h
      cases v <;> obtain ⟨s, ⟨i, rfl, rfl⟩, rfl⟩ := h <;>
        have hi : i = 0 := Subsingleton.elim _ _ <;> subst i <;> exact ⟨rfl, rfl⟩ }
  have hf : (project f).LocallySurjective := by
    apply project_surjective f
    · intro v _
      fin_cases v
      · exact ⟨.inl (0 : Fin 1), True.intro, rfl⟩
      · exact ⟨.inr (0 : Fin 1), True.intro, rfl⟩
    · intro v h; exact False.elim h
    · intro v d t h
      obtain ⟨rfl, rfl⟩ := h
      cases v <;> exact ⟨.inr 0, ⟨.inr 0, ⟨0, rfl, rfl⟩, rfl⟩, rfl⟩
  exact (SumEvaluation.eval_cover E (project f) hf).symm

private noncomputable def doublePattern {A : RankedSet} {k : ℕ}
    (x y : Data A k) (a : A k) (j : Fin (k + 1)) :=
  relabel (letterSubstitution (atomic a))
    (normalContext x.1 (fun l => pairSystem (x.2 l) (if l = j then y.2 l else x.2 l))).system

private theorem eval_double {A : RankedSet} (E : SetAlgebra A) {k : ℕ}
    (x y : Data A k) (a : A k) (j : Fin (k + 1)) :
    E.eval 0 (flatten (doublePattern x y a j)) =
      value E a (x.1, fun l => meet E (x.2 l) (if l = j then y.2 l else x.2 l)) := by
  classical
  have he : relabel E.eval (doublePattern x y a j) =
      relabel (letterSubstitution a)
        (normalContext x.1 (fun l => meet E (x.2 l) (if l = j then y.2 l else x.2 l))).system := by
    dsimp only [doublePattern, relabel, normalContext, normalSystem, normalPresentation]
    congr 1
    congr 1
    funext v
    cases v using Fin.cases with
    | zero => exact congrArg (Sigma.mk k) (E.unit k a)
    | succ l => exact congrArg (Sigma.mk 1) (eval_pair E _ _)
  rw [← E.associative, he]
  obtain ⟨c, hc⟩ := plug_atomic_cover
    (normalContext x.1 (fun l => meet E (x.2 l) (if l = j then y.2 l else x.2 l))) a
  exact (SumEvaluation.eval_cover E c hc).symm

private noncomputable def doublePosition {A : RankedSet} {k : ℕ}
    (x y : Data A k) (a : A k) (i : Fin k) (j : Fin (k + 1)) :
    ((v : (doublePattern x y a j).Vertex) × (Inner (doublePattern x y a j) v).Vertex) →
    ((v : (testPattern x y a).Vertex) × (Inner (testPattern x y a) v).Vertex) := by
  classical
  exact fun v => Fin.cases (fun _ => ⟨(0 : Fin (k + 2)), center x a i⟩)
    (fun l u => if l = j ∧ u ≠ (0 : Fin 2) then ⟨l.succ, (0 : Fin 1)⟩
      else ⟨(0 : Fin (k + 2)), embedVertex x a i l.succ⟩) v.1 v.2

private theorem doublePosition_succ {A : RankedSet} {k : ℕ}
    (x y : Data A k) (a : A k) (i : Fin k) (j l : Fin (k + 1)) (u : Fin 2) :
    doublePosition x y a i j ⟨l.succ, u⟩ =
      if l = j ∧ u ≠ (0 : Fin 2) then ⟨l.succ, (0 : Fin 1)⟩
      else ⟨(0 : Fin (k + 2)), embedVertex x a i l.succ⟩ := by
  classical
  change (if l = j ∧ u ≠ (0 : Fin 2) then _ else _) = _
  split <;> simp_all

private theorem double_label {A : RankedSet} {k : ℕ}
    (x y : Data A k) (a : A k) (i : Fin k) (j : Fin (k + 1))
    (v : (v : (doublePattern x y a j).Vertex) × (Inner (doublePattern x y a j) v).Vertex) :
    (Lax369799Proofs.Flattening.graph (testPattern x y a)).label (doublePosition x y a i j v) =
      (Lax369799Proofs.Flattening.graph (doublePattern x y a j)).label v := by
  classical
  obtain ⟨v, u⟩ := v
  cases v using Fin.cases with
  | zero =>
    change (rawDelta x a).label (vertex (rawDelta x a) (index (rawDelta x a) _)) = _
    rw [vertex_index]
    rfl
  | succ l =>
    by_cases h : l = j ∧ u ≠ (0 : Fin 2)
    · simp only [doublePosition_succ, if_pos h]
      change Sigma.mk 1 (y.2 l) = Sigma.mk 1 (if u = (0 : Fin 2) then x.2 l else if l = j then y.2 l else x.2 l)
      rw [if_neg h.2, if_pos h.1]
    · simp only [doublePosition_succ, if_neg h]
      have he := (testMapRaw x y a i x.1 Or.inl (fun _ h => Or.inl h)).label l.succ
      change _ = Sigma.mk 1 (x.2 l) at he
      refine he.trans ?_
      change Sigma.mk 1 (x.2 l) = Sigma.mk 1 (if u = (0 : Fin 2) then x.2 l else if l = j then y.2 l else x.2 l)
      by_cases hu : u = (0 : Fin 2)
      · rw [if_pos hu]
      · rw [if_neg hu, if_neg (fun hl => h ⟨hl, hu⟩)]

private theorem double_root {A : RankedSet} {k : ℕ}
    (x y : Data A k) (a : A k) (i : Fin k) (j : Fin (k + 1))
    (v : (v : (doublePattern x y a j).Vertex) × (Inner (doublePattern x y a j) v).Vertex)
    (h : (Lax369799Proofs.Flattening.graph (doublePattern x y a j)).root v) :
    (Lax369799Proofs.Flattening.graph (testPattern x y a)).root (doublePosition x y a i j v) := by
  classical
  obtain ⟨v, u⟩ := v
  rcases h with h | ⟨h, _⟩
  · cases v using Fin.cases <;> exact False.elim h
  · cases v using Fin.cases with
    | zero =>
      rcases h with h | ⟨_, h⟩
      · exact False.elim (Fin.succ_ne_zero (0 : Fin (k + 1)) h.symm)
      · exact Or.inl (center_root x a i h)
    | succ l =>
      rcases h with h | ⟨h, _⟩
      · have hl : l = 0 := Fin.succ_inj.mp h
        subst l
        by_cases hu : (0 : Fin (k + 1)) = j ∧ u ≠ (0 : Fin 2)
        · simp only [doublePosition_succ, if_pos hu]
          exact Or.inr ⟨Or.inl rfl, True.intro⟩
        · simp only [doublePosition_succ, if_neg hu]
          exact Or.inl (root_root x a)
      · exact False.elim (Fin.succ_ne_zero l h)

private theorem double_no_internal {A : RankedSet} {k : ℕ}
    (x y : Data A k) (a : A k) (j : Fin (k + 1))
    (v : (doublePattern x y a j).Vertex) (u w : (Inner (doublePattern x y a j) v).Vertex)
    (d : ℕ) : ¬ (Inner (doublePattern x y a j) v).graph.edge u d (.inl w) := by
  cases v using Fin.cases with
  | zero => rintro ⟨i, _, h⟩; cases h
  | succ l => rintro ⟨_, h⟩; cases h

private theorem double_exit {A : RankedSet} {k : ℕ}
    (x y : Data A k) (a : A k) (j : Fin (k + 1))
    (v : (doublePattern x y a j).Vertex) (u : (Inner (doublePattern x y a j) v).Vertex)
    (d : ℕ) (e : Fin ((doublePattern x y a j).graph.label v).1)
    (h : (Inner (doublePattern x y a j) v).graph.edge u d (.inr e)) : d = e.val := by
  cases v using Fin.cases with
  | zero => obtain ⟨i, hd, he⟩ := h; cases Sum.inr.inj he; exact hd
  | succ l =>
    have he : e = (0 : Fin 1) := Subsingleton.elim (α := Fin 1) _ _
    exact h.1.trans (congrArg Fin.val he).symm

private theorem double_transition {A : RankedSet} {k : ℕ}
    (x y : Data A k) (a : A k) (i : Fin k) (j : Fin (k + 1))
    (hji : j = 0 ∨ j = i.succ)
    (v w : (v : (doublePattern x y a j).Vertex) × (Inner (doublePattern x y a j) v).Vertex)
    (d : ℕ)
    (h : (relabel (letterSubstitution a) (normalContext x.1 x.2).system).graph.edge
      v.1 d (.inl w.1)) :
    (Lax369799Proofs.Flattening.graph (testPattern x y a)).edge
      (doublePosition x y a i j v) d (.inl (doublePosition x y a i j w)) := by
  classical
  obtain ⟨v, u⟩ := v
  obtain ⟨w, z⟩ := w
  cases v using Fin.cases with
  | zero =>
    rcases h with ⟨r, rfl, he⟩ | ⟨r, hr, rfl, he⟩
    · have hw := Sum.inl.inj he
      dsimp only at hw
      subst w
      by_cases hz : r.succ = j ∧ z ≠ (0 : Fin 2)
      · have hri : r = i := by
          rcases hji with hj | hj
          · exact False.elim (Fin.succ_ne_zero r (hz.1.trans hj))
          · exact Fin.succ_inj.mp (hz.1.trans hj)
        subst r
        simp only [doublePosition_succ, if_pos hz]
        exact Or.inr ⟨i, edge_exit x a i,
          Or.inl ⟨⟨i.succ.succ, (0 : Fin 1)⟩, Or.inl ⟨i, rfl, rfl⟩, True.intro, rfl⟩⟩
      · simp only [doublePosition_succ, if_neg hz]
        exact Or.inl ⟨unary x a i r, edge_out x a i r, rfl⟩
    · have hw := Sum.inl.inj he
      dsimp only at hw
      subst w
      exact Or.inl ⟨center x a i, edge_loop x a i r hr, rfl⟩
  | succ l =>
    obtain ⟨rfl, he⟩ := h
    have hw := Sum.inl.inj he
    dsimp only at hw
    subst w
    by_cases hu : l = j ∧ u ≠ (0 : Fin 2)
    · simp only [doublePosition_succ, if_pos hu]
      exact Or.inr ⟨(0 : Fin 1), ⟨(0 : Fin 1), rfl, rfl⟩,
        Or.inl ⟨⟨(0 : Fin (k + 2)), center x a i⟩, ⟨rfl, rfl⟩, center_initial x a i, rfl⟩⟩
    · simp only [doublePosition_succ, if_neg hu]
      cases l using Fin.cases with
      | zero => exact Or.inl ⟨center x a i, edge_root x a i, rfl⟩
      | succ l => exact Or.inl ⟨center x a i, edge_back x a i l, rfl⟩

private noncomputable def doubleMap {A : RankedSet} {k : ℕ}
    (x y : Data A k) (a : A k) (i : Fin k) (j : Fin (k + 1))
    (hji : j = 0 ∨ j = i.succ) :
    Map (Lax369799Proofs.Flattening.graph (doublePattern x y a j))
      (Lax369799Proofs.Flattening.graph (testPattern x y a)) where
  toFun := doublePosition x y a i j
  label := double_label x y a i j
  initial := fun _ h => False.elim h.1
  root := double_root x y a i j
  edge := by
    intro v d t h
    rcases h with ⟨w, hw, _⟩ | ⟨e, he, h⟩
    · exact False.elim (double_no_internal x y a j v.1 v.2 w d hw)
    · rcases h with ⟨w, hw, _, rfl⟩ | ⟨z, _, _⟩
      · rw [double_exit x y a j v.1 v.2 d e he]
        exact double_transition x y a i j hji v w e.val hw
      · exact Fin.elim0 z

/--
---
conclusion: Lax369799.ExtremalContexts.delta_piece_comparison
---
Duplicate the selected unary piece, using the test context's value on
its second copy. Evaluation of that pair is a meet. The resulting
subsystem embeds into the test of Delta, so minimality forces the
original unary value below the test context's unary value.
-/
theorem delta_piece_comparison {A : RankedSet} (E : SetAlgebra A) (f : A 0)
    {k : ℕ} (hk : 1 ≤ k) (x y : Data A k) (a : A k)
    (hx : IsExtremal E f a x) (hy : Accepts E f (E.eval k (delta x.1 x.2 a)) y) :
    ∀ j, Below E (x.2 j) (y.2 j) := by
  classical
  intro j
  obtain ⟨i, hji⟩ : ∃ i : Fin k, j = 0 ∨ j = i.succ := by
    cases j using Fin.cases with
    | zero => exact ⟨⟨0, by omega⟩, Or.inl rfl⟩
    | succ i => exact ⟨i, Or.inr rfl⟩
  let z : Data A k := (x.1, fun l => meet E (x.2 l) (if l = j then y.2 l else x.2 l))
  have hm := E.morphism 0 (flatten (doublePattern x y a j))
    (plug (normalContext y.1 y.2) (delta x.1 x.2 a)) ⟨trimMap (doubleMap x y a i j hji)⟩
  rw [eval_double E x y a j,
    Evaluation.context_evaluation E (normalContext y.1 y.2) (delta x.1 x.2 a)] at hm
  have ha : Accepts E f a z := (SetAlgebraTheorems.order_laws E 0).2.2.1 _ _ _ hy hm
  have hz : DataBelow E z x := by
    refine ⟨id, Set.Subset.rfl, fun l => ?_⟩
    exact ((SetAlgebraTheorems.order_laws E 1).2.2.2 _ _ _).mp
      ((SetAlgebraTheorems.order_laws E 1).1 (z.2 l)) |>.1
  have hj := (hx.2 z hz ha).2.2 j
  change Below E (x.2 j) (meet E (x.2 j) (if j = j then y.2 j else x.2 j)) at hj
  rw [if_pos rfl] at hj
  exact ((SetAlgebraTheorems.order_laws E 1).2.2.2 _ _ _).mp hj |>.2

/--
---
conclusion: Lax369799.ExtremalContexts.delta_below
---
Normalize an arbitrary accepting test context. Boundary and unary-piece
comparisons put the extremal context below its normal form. Acceptance
of the original letter then transfers to this test, and order separation
establishes the required inequality.
-/
theorem delta_below {A : RankedSet} (E : SetAlgebra A) (f : A 0)
    (hp : Lax369799.AutomatonProperty.PlantInvariant E f)
    (hs : Lax369799.AutomatonProperty.OrderSeparating E f) {k : ℕ} (hk : 2 ≤ k)
    (x : Data A k) (a : A k) (hx : IsExtremal E f a x) :
    Below E (E.eval k (delta x.1 x.2 a)) a := by
  apply hs
  intro C hC
  let y : Data A k := (Lax369799.AlgebraicDecomposition.plantedBoundary C,
    Lax369799.AlgebraicDecomposition.pieceValue E C)
  have hy : Accepts E f (E.eval k (delta x.1 x.2 a)) y := by
    change Below E f (E.eval 0 (plug (normalContext _ _) (atomic _)))
    rw [AlgebraicDecomposition.algebraic_decomposition E C]
    exact (hp _).mp hC
  have hb := delta_boundary_comparison E f (by omega) x y a hx hy
  have hm := delta_piece_comparison E f (by omega) x y a hx hy
  have hya : Accepts E f a y := (SetAlgebraTheorems.order_laws E 0).2.2.1 _ _ _ hx.1
    (NormalMonotonicity.data_monotone E x y ⟨hb.1, hb.2, hm⟩ a)
  change Below E f (E.eval 0 (plug (normalContext _ _) (atomic a))) at hya
  rw [AlgebraicDecomposition.algebraic_decomposition E C a] at hya
  exact (hp _).mpr hya

end Lax369799Proofs.DeltaComparison
