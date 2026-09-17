import Lax369799Proofs.FiniteDeltaContext
import Lax369799Proofs.FiniteOrderedAlgebra

set_option backward.isDefEq.respectTransparency false

namespace Lax369799Proofs.FiniteDeltaComparison
open Lax369799.RankedSystems (RankedSet Presentation)
open Lax369799.FinitePresentations Lax369799.FiniteContexts Lax369799.FiniteContextualOrder
open Lax369799.FiniteSyntacticAlgebra
open Lax369799.ExtremalContexts (Boundary Data)
open Lax369799.FiniteNormalForms (normalContext)
open Lax369799.FiniteExtremal
open Lax369799Proofs.Pullbacks (Map)
open Lax369799Proofs.FiniteNormalForms (letterSubstitution)

private noncomputable def index {A : RankedSet} {n : ℕ} {V : Type} [Fintype V]
    (G : Presentation A n V) : V ≃ (enumerate G).Vertex :=
  Fintype.equivFin V

private noncomputable def vertex {A : RankedSet} {n : ℕ} {V : Type} [Fintype V]
    (G : Presentation A n V) := (index G).symm

private theorem vertex_index {A : RankedSet} {n : ℕ} {V : Type} [Fintype V]
    (G : Presentation A n V) (v : V) : vertex G (index G v) = v := (index G).symm_apply_apply v

private noncomputable def rawDelta {A : RankedSet} {k : ℕ}
    (x : Data A k) (a : A k) := flattenPresentation (deltaPattern x.1 x.2 a).graph

private noncomputable def rootVertex {A : RankedSet} {k : ℕ} (x : Data A k) (a : A k) :
    (delta x.1 x.2 a).Vertex := index (rawDelta x a) ⟨(0 : Fin (k + 1)), (0 : Fin 1)⟩

private noncomputable def center {A : RankedSet} {k : ℕ} (x : Data A k) (a : A k) (i : Fin k) :
    (delta x.1 x.2 a).Vertex := index (rawDelta x a) ⟨i.succ, (0 : Fin (k + 1))⟩

private noncomputable def unary {A : RankedSet} {k : ℕ} (x : Data A k) (a : A k) (i j : Fin k) :
    (delta x.1 x.2 a).Vertex := index (rawDelta x a) ⟨i.succ, j.succ⟩

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
      (flattenPresentation (testPattern x y a).graph) where
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


private theorem test_bound {A : RankedSet} (L : Lax369799.Algebras.Language A)
    (E : Algebra (Carrier (Lax369799.FiniteAcceptance.Accepting L)))
    (hE : ∀ n (S : FiniteSystem (FiniteSystem A) n),
      E.eval n (relabel (quotientMap (Lax369799.FiniteAcceptance.Accepting L)) S) =
        quotientMap (Lax369799.FiniteAcceptance.Accepting L) n (flatten S))
    {k : ℕ} (x y : Data (Carrier (Lax369799.FiniteAcceptance.Accepting L)) k)
    (a : Carrier (Lax369799.FiniteAcceptance.Accepting L) k) (i : Fin k) (B : Boundary k)
    (hr : B.root → x.1.root ∨ y.1.root)
    (hl : ∀ j ∈ B.loops, j ∈ x.1.loops ∨ (j = i ∧ j ∈ y.1.loops)) :
    ClassBelow (Lax369799.FiniteAcceptance.Accepting L)
      (value E (E.eval k (delta x.1 x.2 a)) y) (value E a (B, x.2)) := by
  have hm := FiniteOuterMorphisms.evaluation_morphism L E hE
    (FiniteMorphisms.toEnumeration (testMapRaw x y a i B hr hl))
  change ClassBelow _ (E.eval 0 (plug (normalContext y.1 y.2) (delta x.1 x.2 a)))
    (E.eval 0 (relabel (letterSubstitution a) (normalContext B x.2).system)) at hm
  rw [FiniteEvaluation.context_evaluation E (normalContext y.1 y.2) (delta x.1 x.2 a)] at hm
  rw [← E.isomorphic 0 _ _ (FiniteNormalForms.plug_atomic_iso (normalContext B x.2) a)] at hm
  exact hm

/--
---
conclusion: Lax369799.FiniteExtremal.delta_boundary_comparison
---
An extra root or loop in an accepting test supplies a subsystem morphism
that permits adding that feature to the original extremal datum. Minimality
forces the feature to have been present already.
-/
theorem delta_boundary_comparison {A : RankedSet} (L : Lax369799.Algebras.Language A)
    (E : Algebra (Carrier (Lax369799.FiniteAcceptance.Accepting L)))
    (hE : ∀ n (S : FiniteSystem (FiniteSystem A) n),
      E.eval n (relabel (quotientMap (Lax369799.FiniteAcceptance.Accepting L)) S) =
        quotientMap (Lax369799.FiniteAcceptance.Accepting L) n (flatten S))
    {k : ℕ} (hk : 1 ≤ k) (x y : Data (Carrier (Lax369799.FiniteAcceptance.Accepting L)) k)
    (a : Carrier (Lax369799.FiniteAcceptance.Accepting L) k)
    (hx : IsExtremal (Lax369799.FiniteAcceptance.Accepting L) E a x)
    (hy : Accepts (Lax369799.FiniteAcceptance.Accepting L) E (E.eval k (delta x.1 x.2 a)) y) :
    (y.1.root → x.1.root) ∧ y.1.loops ⊆ x.1.loops := by
  let F := Lax369799.FiniteAcceptance.Accepting L
  have hrefl := (FiniteContextualOrder.class_order F 1).1
  have hup := (FiniteSyntacticAlgebra.accepting_classes F (FiniteAcceptance.accepting_isomorphic L)).2
  constructor
  · intro hyr
    let i : Fin k := ⟨0, by omega⟩
    let B : Boundary k := ⟨True, x.1.loops⟩
    have hz : DataBelow F (B, x.2) x := ⟨fun _ => True.intro, Set.Subset.rfl, fun j => hrefl _⟩
    have ha : Accepts F E a (B, x.2) := hup _ _ hy
      (test_bound L E hE x y a i B (fun _ => Or.inr hyr) (fun _ h => Or.inl h))
    exact (hx.2 (B, x.2) hz ha).1 True.intro
  · intro i hi
    let B : Boundary k := ⟨x.1.root, insert i x.1.loops⟩
    have hz : DataBelow F (B, x.2) x := ⟨id, Set.subset_insert i _, fun j => hrefl _⟩
    have ha : Accepts F E a (B, x.2) := hup _ _ hy
      (test_bound L E hE x y a i B Or.inl (by
        intro j hj
        rcases hj with rfl | hj
        · exact Or.inr ⟨rfl, hi⟩
        · exact Or.inl hj))
    exact (hx.2 (B, x.2) hz ha).2.1 (Or.inl rfl)

private def pairSystem {A : RankedSet} (b c : A 1) : FiniteSystem A 1 where
  size := 2
  graph := {
    label := fun v => ⟨1, if v = 0 then b else c⟩
    initial := Set.univ
    root := ∅
    edge := fun _ d t => d = 0 ∧ t = .inr 0
    direction_valid := by rintro v d t ⟨rfl, _⟩; exact Nat.zero_lt_one }

private theorem eval_pair {A : RankedSet} (E : Algebra A) (b c : A 1) :
    E.eval 1 (pairSystem b c) = sumValue E b c := by
  apply E.isomorphic
  refine ⟨{
    vertex := Equiv.refl _
    label := ?_
    initial := fun _ => Iff.rfl
    root := fun _ => Iff.rfl
    edge := ?_ }⟩
  · intro v
    fin_cases v <;> rfl
  · intro v d t
    change (∃ i : Fin 1, d = i.val ∧ Sum.map (Equiv.refl _) id t = .inr i) ↔
      (d = 0 ∧ t = .inr 0)
    constructor
    · rintro ⟨i, hi, he⟩
      fin_cases i
      cases t <;> simp_all
    · rintro ⟨rfl, rfl⟩
      exact ⟨0, rfl, rfl⟩

private noncomputable def doublePattern {A : RankedSet} {k : ℕ}
    (x y : Data A k) (a : A k) (j : Fin (k + 1)) :=
  relabel (letterSubstitution (atomic a))
    (normalContext x.1 (fun l => pairSystem (x.2 l) (if l = j then y.2 l else x.2 l))).system

private theorem eval_double {A : RankedSet} {F : ClosedProperty A} (E : Algebra (Carrier F)) {k : ℕ}
    (x y : Data (Carrier F) k) (a : Carrier F k) (j : Fin (k + 1)) :
    E.eval 0 (flatten (doublePattern x y a j)) =
      value E a (x.1, fun l => sumValue E (x.2 l) (if l = j then y.2 l else x.2 l)) := by
  classical
  have he : relabel E.eval (doublePattern x y a j) =
      relabel (letterSubstitution a)
        (normalContext x.1 (fun l => sumValue E (x.2 l) (if l = j then y.2 l else x.2 l))).system := by
    dsimp only [doublePattern, relabel, normalContext, ofSetSystem,
      Lax369799.ExtremalContexts.normalContext, Lax369799.ExtremalContexts.normalSystem,
      Lax369799.ExtremalContexts.normalPresentation]
    congr 1
    congr 1
    funext v
    cases v using Fin.cases with
    | zero => exact congrArg (Sigma.mk k) (E.unit k a)
    | succ l => exact congrArg (Sigma.mk 1) (eval_pair E _ _)
  rw [← E.associative, he]
  exact (E.isomorphic 0 _ _ (FiniteNormalForms.plug_atomic_iso
    (normalContext x.1 (fun l => sumValue E (x.2 l) (if l = j then y.2 l else x.2 l))) a)).symm

private noncomputable def doublePosition {A : RankedSet} {k : ℕ}
    (x y : Data A k) (a : A k) (i : Fin k) (j : Fin (k + 1)) :
    ((v : (doublePattern x y a j).Vertex) × (Inner (doublePattern x y a j).graph v).Vertex) →
    ((v : (testPattern x y a).Vertex) × (Inner (testPattern x y a).graph v).Vertex) := by
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
    (v : (v : (doublePattern x y a j).Vertex) × (Inner (doublePattern x y a j).graph v).Vertex) :
    (flattenPresentation (testPattern x y a).graph).label (doublePosition x y a i j v) =
      (flattenPresentation (doublePattern x y a j).graph).label v := by
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
    (v : (v : (doublePattern x y a j).Vertex) × (Inner (doublePattern x y a j).graph v).Vertex)
    (h : (flattenPresentation (doublePattern x y a j).graph).root v) :
    (flattenPresentation (testPattern x y a).graph).root (doublePosition x y a i j v) := by
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
    (v : (doublePattern x y a j).Vertex) (u w : (Inner (doublePattern x y a j).graph v).Vertex)
    (d : ℕ) : ¬ (Inner (doublePattern x y a j).graph v).graph.edge u d (.inl w) := by
  cases v using Fin.cases with
  | zero => rintro ⟨i, _, h⟩; cases h
  | succ l => rintro ⟨_, h⟩; cases h

private theorem double_exit {A : RankedSet} {k : ℕ}
    (x y : Data A k) (a : A k) (j : Fin (k + 1))
    (v : (doublePattern x y a j).Vertex) (u : (Inner (doublePattern x y a j).graph v).Vertex)
    (d : ℕ) (e : Fin ((doublePattern x y a j).graph.label v).1)
    (h : (Inner (doublePattern x y a j).graph v).graph.edge u d (.inr e)) : d = e.val := by
  cases v using Fin.cases with
  | zero => obtain ⟨i, hd, he⟩ := h; cases Sum.inr.inj he; exact hd
  | succ l =>
    have he : e = (0 : Fin 1) := Subsingleton.elim (α := Fin 1) _ _
    exact h.1.trans (congrArg Fin.val he).symm

private theorem double_transition {A : RankedSet} {k : ℕ}
    (x y : Data A k) (a : A k) (i : Fin k) (j : Fin (k + 1))
    (hji : j = 0 ∨ j = i.succ)
    (v w : (v : (doublePattern x y a j).Vertex) × (Inner (doublePattern x y a j).graph v).Vertex)
    (d : ℕ)
    (h : (relabel (letterSubstitution a) (normalContext x.1 x.2).system).graph.edge
      v.1 d (.inl w.1)) :
    (flattenPresentation (testPattern x y a).graph).edge
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
    Map (flattenPresentation (doublePattern x y a j).graph)
      (flattenPresentation (testPattern x y a).graph) where
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
conclusion: Lax369799.FiniteExtremal.delta_piece_comparison
---
Duplicate one unary piece using a binary meet pattern and embed the result
into the accepting test of Delta. Extremality forces the original unary
value below the testing value.
-/
theorem delta_piece_comparison {A : RankedSet} (L : Lax369799.Algebras.Language A)
    (E : Algebra (Carrier (Lax369799.FiniteAcceptance.Accepting L)))
    (hE : ∀ n (S : FiniteSystem (FiniteSystem A) n),
      E.eval n (relabel (quotientMap (Lax369799.FiniteAcceptance.Accepting L)) S) =
        quotientMap (Lax369799.FiniteAcceptance.Accepting L) n (flatten S))
    {k : ℕ} (hk : 1 ≤ k) (x y : Data (Carrier (Lax369799.FiniteAcceptance.Accepting L)) k)
    (a : Carrier (Lax369799.FiniteAcceptance.Accepting L) k)
    (hx : IsExtremal (Lax369799.FiniteAcceptance.Accepting L) E a x)
    (hy : Accepts (Lax369799.FiniteAcceptance.Accepting L) E (E.eval k (delta x.1 x.2 a)) y) :
    ∀ j, ClassBelow (Lax369799.FiniteAcceptance.Accepting L) (x.2 j) (y.2 j) := by
  classical
  let F := Lax369799.FiniteAcceptance.Accepting L
  intro j
  obtain ⟨i, hji⟩ : ∃ i : Fin k, j = 0 ∨ j = i.succ := by
    cases j using Fin.cases with
    | zero => exact ⟨⟨0, by omega⟩, Or.inl rfl⟩
    | succ i => exact ⟨i, Or.inr rfl⟩
  let z : Data (Carrier F) k := (x.1, fun l => sumValue E (x.2 l) (if l = j then y.2 l else x.2 l))
  have hm := FiniteOuterMorphisms.evaluation_morphism L E hE
    (FiniteMorphisms.enumerateMap (doubleMap x y a i j hji))
  change ClassBelow F (E.eval 0 (plug (normalContext y.1 y.2) (delta x.1 x.2 a)))
    (E.eval 0 (flatten (doublePattern x y a j))) at hm
  rw [eval_double E x y a j,
    FiniteEvaluation.context_evaluation E (normalContext y.1 y.2) (delta x.1 x.2 a)] at hm
  have hup := (FiniteSyntacticAlgebra.accepting_classes F (FiniteAcceptance.accepting_isomorphic L)).2
  have ha : Accepts F E a z := hup _ _ hy hm
  have hz : DataBelow F z x := by
    refine ⟨id, Set.Subset.rfl, fun l => ?_⟩
    exact (FiniteOrderedAlgebra.sum_value_meet L E hE _ _ _).mp
      ((FiniteContextualOrder.class_order F 1).1 (z.2 l)) |>.1
  have hj := (hx.2 z hz ha).2.2 j
  change ClassBelow F (x.2 j) (sumValue E (x.2 j) (if j = j then y.2 j else x.2 j)) at hj
  rw [if_pos rfl] at hj
  exact (FiniteOrderedAlgebra.sum_value_meet L E hE _ _ _).mp hj |>.2

/--
---
conclusion: Lax369799.FiniteExtremal.delta_below
---
Normalize each accepting algebra context. Boundary and unary comparisons
put the extremal datum below its normal form. Monotonicity and planting
invariance transfer acceptance back to the original value. Order separation
then gives the required contextual inequality.
-/
theorem delta_below {A : RankedSet} (L : Lax369799.Algebras.Language A)
    (E : Algebra (Carrier (Lax369799.FiniteAcceptance.Accepting L)))
    (hE : ∀ n (S : FiniteSystem (FiniteSystem A) n),
      E.eval n (relabel (quotientMap (Lax369799.FiniteAcceptance.Accepting L)) S) =
        quotientMap (Lax369799.FiniteAcceptance.Accepting L) n (flatten S))
    {k : ℕ} (hk : 2 ≤ k) (x : Data (Carrier (Lax369799.FiniteAcceptance.Accepting L)) k)
    (a : Carrier (Lax369799.FiniteAcceptance.Accepting L) k)
    (hx : IsExtremal (Lax369799.FiniteAcceptance.Accepting L) E a x) :
    ClassBelow (Lax369799.FiniteAcceptance.Accepting L) (E.eval k (delta x.1 x.2 a)) a := by
  let F := Lax369799.FiniteAcceptance.Accepting L
  have hF := FiniteAcceptance.accepting_isomorphic L
  have hc := fun n (S T : FiniteSystem (Carrier F) n) f hf =>
    FiniteOuterMorphisms.evaluation_cover L E hE (S := S) (T := T) f hf
  apply FiniteEvaluation.order_separating F hF E hE
  intro C hC
  let y : Data (Carrier F) k := (Lax369799.FiniteNormalForms.plantedBoundary C,
    Lax369799.FiniteNormalForms.pieceValue E C)
  have hy : Accepts F E (E.eval k (delta x.1 x.2 a)) y := by
    change AcceptingClass F (E.eval 0 (plug (normalContext _ _) (atomic _)))
    rw [FiniteNormalForms.algebraic_decomposition E hc C]
    exact (FinitePlant.accepting_evaluation_plant L E hE _).mpr hC
  have hb := delta_boundary_comparison L E hE (by omega) x y a hx hy
  have hm := delta_piece_comparison L E hE (by omega) x y a hx hy
  have hya : Accepts F E a y := (FiniteSyntacticAlgebra.accepting_classes F hF).2 _ _ hx.1
    (FiniteExtremal.data_monotone L E hE x y ⟨hb.1, hb.2, hm⟩ a)
  change AcceptingClass F (E.eval 0 (plug (normalContext _ _) (atomic a))) at hya
  rw [FiniteNormalForms.algebraic_decomposition E hc C a] at hya
  exact (FinitePlant.accepting_evaluation_plant L E hE _).mp hya

end Lax369799Proofs.FiniteDeltaComparison
