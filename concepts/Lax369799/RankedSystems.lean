import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Fintype.Sigma
import Mathlib.Logic.Relation
import Mathlib.Data.Set.Finite.Basic

/-!
---
title: Ranked sets, set-systems, and systems
type: definition
---
A ranked set is a family of sets indexed by natural numbers. A set-system
has finitely many labelled vertices, initial and root vertices, and edges
with a direction and either a vertex or a variable as target. Every vertex
is reachable from an initial or root vertex. A system has one initial
vertex, no roots, and exactly one successor in every available direction.

This is the earlier reachable interface. The revised Section 2.2 allows
unreachable vertices in set-systems (`FinitePresentations`) and requires
all output variables of a deterministic system to be reachable
(`SupportedSystems`). Finite vertex sets are enumerated by
`Fin size`; directions and variables use zero-based indices. `Presentation`
allows an arbitrary finite vertex type when constructing these objects.
-/

namespace Lax369799.RankedSystems

abbrev RankedSet := ℕ → Type
abbrev Symbol (A : RankedSet) := (n : ℕ) × A n
abbrev RankedMap (A B : RankedSet) := ∀ n, A n → B n

def RankwiseFinite (A : RankedSet) : Prop := ∀ n, Finite (A n)

structure Presentation (A : RankedSet) (n : ℕ) (V : Type) where
  label : V → Symbol A
  initial : Set V
  root : Set V
  edge : V → ℕ → V ⊕ Fin n → Prop
  direction_valid : ∀ v d t, edge v d t → d < (label v).1

def Presentation.Step {A : RankedSet} {n : ℕ} {V : Type}
    (S : Presentation A n V) (v w : V) : Prop :=
  ∃ d, S.edge v d (.inl w)

def Presentation.Reachable {A : RankedSet} {n : ℕ} {V : Type}
    (S : Presentation A n V) (v : V) : Prop :=
  ∃ r, (r ∈ S.initial ∨ r ∈ S.root) ∧ Relation.ReflTransGen S.Step r v

structure SetSystem (A : RankedSet) (n : ℕ) where
  size : ℕ
  graph : Presentation A n (Fin size)
  reachable : ∀ v, graph.Reachable v

abbrev SetSystem.Vertex {A : RankedSet} {n : ℕ} (S : SetSystem A n) := Fin S.size

/-- Restrict to reachable vertices and enumerate the resulting finite set. -/
noncomputable def trim {A : RankedSet} {n : ℕ} {V : Type} [Fintype V]
    (S : Presentation A n V) : SetSystem A n := by
  classical
  let W := {v : V // S.Reachable v}
  let e : W ≃ Fin (Fintype.card W) := Fintype.equivFin W
  let g : Fin (Fintype.card W) → V := fun v => (e.symm v).val
  let G : Presentation A n (Fin (Fintype.card W)) := {
    label := fun v => S.label (g v)
    initial := fun v => S.initial (g v)
    root := fun v => S.root (g v)
    edge := fun v d t => S.edge (g v) d (Sum.map g id t)
    direction_valid := fun v d t h => S.direction_valid (g v) d _ h }
  refine ⟨Fintype.card W, G, ?_⟩
  intro v
  obtain ⟨r, hr, hp⟩ := (e.symm v).property
  have rr : S.Reachable r := ⟨r, hr, .refl⟩
  refine ⟨e ⟨r, rr⟩, ?_, ?_⟩
  · change S.initial (g (e ⟨r, rr⟩)) ∨ S.root (g (e ⟨r, rr⟩))
    simp only [g, Equiv.symm_apply_apply]
    exact hr
  · have liftPath : ∀ {a b : V} (h : Relation.ReflTransGen S.Step a b)
        (ha : S.Reachable a) (hb : S.Reachable b),
        Relation.ReflTransGen G.Step (e ⟨a, ha⟩) (e ⟨b, hb⟩) := by
      intro a b h
      induction h with
      | refl => intro ha hb; exact .refl
      | @tail b c h hbc ih =>
        intro ha hc
        have hb : S.Reachable b := by
          obtain ⟨r, hr, hp⟩ := ha
          exact ⟨r, hr, hp.trans h⟩
        apply Relation.ReflTransGen.tail (ih ha hb)
        obtain ⟨d, hd⟩ := hbc
        exact ⟨d, by simpa [G, g] using hd⟩
    simpa using liftPath hp rr (e.symm v).property

def SetSystem.Deterministic {A : RankedSet} {n : ℕ} (S : SetSystem A n) : Prop :=
  (∃ i, S.graph.initial = {i}) ∧ S.graph.root = ∅ ∧
  ∀ v d, d < (S.graph.label v).1 → ∃! t, S.graph.edge v d t

abbrev System (A : RankedSet) (n : ℕ) := {S : SetSystem A n // S.Deterministic}

def relabel {A B : RankedSet} (f : RankedMap A B) {n : ℕ}
    (S : SetSystem A n) : SetSystem B n where
  size := S.size
  graph := { S.graph with label := fun v => ⟨(S.graph.label v).1,
    f _ (S.graph.label v).2⟩ }
  reachable := S.reachable

def relabelSystem {A B : RankedSet} (f : RankedMap A B) {n : ℕ}
    (S : System A n) : System B n := ⟨relabel f S.val, S.property⟩

def atomic {A : RankedSet} {n : ℕ} (a : A n) : SetSystem A n where
  size := 1
  graph := {
    label := fun _ => ⟨n, a⟩
    initial := Set.univ
    root := ∅
    edge := fun _ d t => ∃ i : Fin n, d = i.val ∧ t = Sum.inr i
    direction_valid := by rintro _ _ _ ⟨i, rfl, rfl⟩; exact i.isLt }
  reachable := fun v => ⟨v, Or.inl (Set.mem_univ v), .refl⟩

def atomicSystem {A : RankedSet} {n : ℕ} (a : A n) : System A n :=
  ⟨atomic a, by
    change (∃ i : Fin 1, Set.univ = {i}) ∧ (∅ : Set (Fin 1)) = ∅ ∧ _
    refine ⟨⟨0, by ext v; simp [Subsingleton.elim v 0]⟩, rfl, ?_⟩
    intro v d hd
    refine ⟨Sum.inr ⟨d, hd⟩, ⟨⟨d, hd⟩, rfl, rfl⟩, ?_⟩
    rintro t ⟨i, hi, rfl⟩
    congr 1
    exact Fin.ext hi.symm⟩

noncomputable def uproot {A : RankedSet} {n : ℕ} (S : SetSystem A n) : SetSystem A n :=
  trim { S.graph with initial := S.graph.root, root := ∅ }

def plant {A : RankedSet} {n : ℕ} (S : SetSystem A n) : SetSystem A n where
  size := S.size
  graph := { S.graph with initial := ∅, root := S.graph.root ∪ S.graph.initial }
  reachable := by
    intro v
    obtain ⟨r, hr, hp⟩ := S.reachable v
    exact ⟨r, Or.inr (hr.elim Or.inr Or.inl), hp⟩

noncomputable def sum {A : RankedSet} {n : ℕ} (S T : SetSystem A n) : SetSystem A n :=
  trim {
    label := Sum.elim S.graph.label T.graph.label
    initial := Sum.elim S.graph.initial T.graph.initial
    root := Sum.elim S.graph.root T.graph.root
    edge := fun v d t => match v with
      | .inl v => ∃ t', S.graph.edge v d t' ∧ t = Sum.map Sum.inl id t'
      | .inr v => ∃ t', T.graph.edge v d t' ∧ t = Sum.map Sum.inr id t'
    direction_valid := by
      intro v d t h
      cases v with
      | inl v => obtain ⟨t', ht, _⟩ := h; exact S.graph.direction_valid v d t' ht
      | inr v => obtain ⟨t', ht, _⟩ := h; exact T.graph.direction_valid v d t' ht }

end Lax369799.RankedSystems
