import Lax369799.RankedSystems

/-!
---
title: Finite presentations without reachability pruning
type: definition
---
Finite presentations retain every vertex during substitution. Reachability
is an additional property, rather than a restriction on intermediate
presentations. This distinction is needed for associativity when labels
may themselves contain roots: an intermediate unreachable vertex may
carry a label with a root that becomes visible at the next substitution.
-/

namespace Lax369799.FinitePresentations
open RankedSystems

structure FiniteSystem (A : RankedSet) (n : ℕ) where
  size : ℕ
  graph : Presentation A n (Fin size)

abbrev FiniteSystem.Vertex {A : RankedSet} {n : ℕ} (S : FiniteSystem A n) := Fin S.size

def Reachable {A : RankedSet} {n : ℕ} (S : FiniteSystem A n) : Prop :=
  ∀ v, S.graph.Reachable v

def ofSetSystem {A : RankedSet} {n : ℕ} (S : SetSystem A n) : FiniteSystem A n :=
  ⟨S.size, S.graph⟩

def atomic {A : RankedSet} {n : ℕ} (a : A n) : FiniteSystem A n :=
  ofSetSystem (RankedSystems.atomic a)

def reindex {A : RankedSet} {n : ℕ} {V W : Type}
    (G : Presentation A n V) (e : V ≃ W) : Presentation A n W where
  label := fun w => G.label (e.symm w)
  initial := fun w => G.initial (e.symm w)
  root := fun w => G.root (e.symm w)
  edge := fun w d t => G.edge (e.symm w) d (Sum.map e.symm id t)
  direction_valid := fun _ d _ h => G.direction_valid _ d _ h

noncomputable def enumerate {A : RankedSet} {n : ℕ} {V : Type} [Fintype V]
    (G : Presentation A n V) : FiniteSystem A n :=
  ⟨Fintype.card V, reindex G (Fintype.equivFin V)⟩

def sumPresentation {A : RankedSet} {n : ℕ} {V W : Type}
    (G : Presentation A n V) (H : Presentation A n W) : Presentation A n (V ⊕ W) where
  label := Sum.elim G.label H.label
  initial := Sum.elim G.initial H.initial
  root := Sum.elim G.root H.root
  edge := fun v d t => match v with
    | .inl v => ∃ s, G.edge v d s ∧ t = Sum.map Sum.inl id s
    | .inr w => ∃ s, H.edge w d s ∧ t = Sum.map Sum.inr id s
  direction_valid := by
    intro v d t h
    cases v with
    | inl v => obtain ⟨s, hs, _⟩ := h; exact G.direction_valid v d s hs
    | inr w => obtain ⟨s, hs, _⟩ := h; exact H.direction_valid w d s hs

noncomputable def sum {A : RankedSet} {n : ℕ} (S T : FiniteSystem A n) : FiniteSystem A n :=
  enumerate (sumPresentation S.graph T.graph)

/-- The presentation with no vertices. -/
def empty (A : RankedSet) (n : ℕ) : FiniteSystem A n where
  size := 0
  graph := {
    label := Fin.elim0
    initial := ∅
    root := ∅
    edge := fun _ _ _ => False
    direction_valid := fun v => Fin.elim0 v }

/-- Turn all initial vertices into roots without deleting vertices. -/
def plant {A : RankedSet} {n : ℕ} (S : FiniteSystem A n) : FiniteSystem A n where
  size := S.size
  graph := { S.graph with initial := ∅, root := S.graph.root ∪ S.graph.initial }

/-- A two-component pattern for disjoint union. -/
def binary {A : RankedSet} {n : ℕ} (a b : A n) : FiniteSystem A n where
  size := 2
  graph := {
    label := Fin.cases ⟨n, a⟩ (fun _ => ⟨n, b⟩)
    initial := Set.univ
    root := ∅
    edge := fun _ d t => ∃ i : Fin n, d = i.val ∧ t = .inr i
    direction_valid := by
      rintro v d t ⟨i, rfl, _⟩
      exact Fin.cases i.isLt (fun _ => i.isLt) v }

abbrev Inner {A : RankedSet} {n : ℕ} {V : Type}
    (P : Presentation (FiniteSystem A) n V) (v : V) := (P.label v).2

def flattenPresentation {A : RankedSet} {n : ℕ} {V : Type}
    (P : Presentation (FiniteSystem A) n V) :
    Presentation A n ((v : V) × (Inner P v).Vertex) where
  label := fun v => (Inner P v.1).graph.label v.2
  initial := fun v => P.initial v.1 ∧ (Inner P v.1).graph.initial v.2
  root := fun v => (Inner P v.1).graph.root v.2 ∨
    (P.root v.1 ∧ (Inner P v.1).graph.initial v.2)
  edge := fun v d t =>
    (∃ w, (Inner P v.1).graph.edge v.2 d (.inl w) ∧ t = .inl ⟨v.1, w⟩) ∨
    (∃ i : Fin (P.label v.1).1, (Inner P v.1).graph.edge v.2 d (.inr i) ∧
      ((∃ w : (v : V) × (Inner P v).Vertex,
        P.edge v.1 i.val (.inl w.1) ∧ (Inner P w.1).graph.initial w.2 ∧ t = .inl w) ∨
       (∃ j, P.edge v.1 i.val (.inr j) ∧ t = .inr j)))
  direction_valid := by
    intro v d t h
    rcases h with ⟨w, hw, _⟩ | ⟨i, hi, _⟩
    · exact (Inner P v.1).graph.direction_valid _ d _ hw
    · exact (Inner P v.1).graph.direction_valid _ d _ hi

noncomputable def flatten {A : RankedSet} {n : ℕ}
    (S : FiniteSystem (FiniteSystem A) n) : FiniteSystem A n :=
  enumerate (flattenPresentation S.graph)

def relabel {A B : RankedSet} (f : RankedMap A B) {n : ℕ}
    (S : FiniteSystem A n) : FiniteSystem B n where
  size := S.size
  graph := {
    label := fun v => ⟨(S.graph.label v).1, f _ (S.graph.label v).2⟩
    initial := S.graph.initial
    root := S.graph.root
    edge := S.graph.edge
    direction_valid := S.graph.direction_valid }

def withLabels {A B : RankedSet} {n : ℕ} (P : FiniteSystem B n)
    (q : ∀ v : P.Vertex, A (P.graph.label v).1) : FiniteSystem A n where
  size := P.size
  graph := {
    label := fun v => ⟨(P.graph.label v).1, q v⟩
    initial := P.graph.initial
    root := P.graph.root
    edge := P.graph.edge
    direction_valid := P.graph.direction_valid }

structure PresentationIso {A : RankedSet} {n : ℕ} {V W : Type}
    (G : Presentation A n V) (H : Presentation A n W) where
  vertex : V ≃ W
  label : ∀ v, H.label (vertex v) = G.label v
  initial : ∀ v, H.initial (vertex v) ↔ G.initial v
  root : ∀ v, H.root (vertex v) ↔ G.root v
  edge : ∀ v d t, H.edge (vertex v) d (Sum.map vertex id t) ↔ G.edge v d t

def Isomorphic {A : RankedSet} {n : ℕ} (S T : FiniteSystem A n) : Prop :=
  Nonempty (PresentationIso S.graph T.graph)

axiom flatten_associative {A : RankedSet} {n : ℕ}
    (S : FiniteSystem (FiniteSystem (FiniteSystem A)) n) :
    Isomorphic (flatten (flatten S)) (flatten (relabel (fun _ T => flatten T) S))

axiom outer_atomic {A : RankedSet} {n : ℕ} (S : FiniteSystem A n) :
    Isomorphic (flatten (atomic S)) S

axiom inner_atomic {A : RankedSet} {n : ℕ} (S : FiniteSystem A n) :
    Isomorphic (flatten (relabel (fun _ a => atomic a) S)) S

axiom flatten_natural {A B : RankedSet} (f : RankedMap A B) {n : ℕ}
    (S : FiniteSystem (FiniteSystem A) n) :
    relabel f (flatten S) = flatten (relabel (fun _ T => relabel f T) S)

axiom flatten_binary {A : RankedSet} {n : ℕ} (S T : FiniteSystem A n) :
    Isomorphic (flatten (binary S T)) (sum S T)

end Lax369799.FinitePresentations
