import Lax369799.RankedSystems

/-!
---
title: Flattening and contexts
type: definition
---
Flattening substitutes a finite set-system at each vertex of a pattern.
Inner transition edges are retained; an inner variable edge is connected
according to the corresponding direction in the pattern. Inner roots remain
roots, and inner initial vertices become roots when the outer vertex is a
root. Unreachable vertices are removed. A context has exactly one vertex
labelled by a hole of the prescribed rank. See Sections 2.6 and 2.8.
-/

namespace Lax369799.Flattening
open RankedSystems

abbrev Inner {A : RankedSet} {n : ℕ} (S : SetSystem (SetSystem A) n)
    (v : S.Vertex) := (S.graph.label v).2

noncomputable def flatten {A : RankedSet} {n : ℕ}
    (S : SetSystem (SetSystem A) n) : SetSystem A n :=
  trim (V := (v : S.Vertex) × (Inner S v).Vertex) {
    label := fun v => (Inner S v.1).graph.label v.2
    initial := fun v => v.1 ∈ S.graph.initial ∧ v.2 ∈ (Inner S v.1).graph.initial
    root := fun v => v.2 ∈ (Inner S v.1).graph.root ∨
      (v.1 ∈ S.graph.root ∧ v.2 ∈ (Inner S v.1).graph.initial)
    edge := fun v d t =>
      (∃ w, (Inner S v.1).graph.edge v.2 d (.inl w) ∧ t = .inl ⟨v.1, w⟩) ∨
      (∃ i : Fin (S.graph.label v.1).1,
        (Inner S v.1).graph.edge v.2 d (.inr i) ∧
        ((∃ w : (v : S.Vertex) × (Inner S v).Vertex,
          S.graph.edge v.1 i.val (.inl w.1) ∧
          w.2 ∈ (Inner S w.1).graph.initial ∧ t = .inl w) ∨
         (∃ j, S.graph.edge v.1 i.val (.inr j) ∧ t = .inr j)))
    direction_valid := by
      intro v d t h
      rcases h with ⟨w, hw, _⟩ | ⟨i, hi, _⟩
      · exact (Inner S v.1).graph.direction_valid v.2 d _ hw
      · exact (Inner S v.1).graph.direction_valid v.2 d _ hi }

abbrev WithHole (A : RankedSet) (k : ℕ) : RankedSet := fun n => A n ⊕ PLift (k = n)

def IsHole {A : RankedSet} {k : ℕ} (a : Symbol (WithHole A k)) : Prop :=
  ∃ h, a.2 = Sum.inr h

structure SetContext (A : RankedSet) (k n : ℕ) where
  system : SetSystem (WithHole A k) n
  one_hole : ∃! v, IsHole (system.graph.label v)

abbrev Context (A : RankedSet) (k n : ℕ) :=
  {C : SetContext A k n // C.system.Deterministic}

def substitution {A : RankedSet} {k : ℕ} (S : SetSystem A k) :
    RankedMap (WithHole A k) (SetSystem A) :=
  fun _ a => match a with
    | .inl a => atomic a
    | .inr ⟨h⟩ => h ▸ S

noncomputable def plug {A : RankedSet} {k n : ℕ}
    (C : SetContext A k n) (S : SetSystem A k) : SetSystem A n :=
  flatten (relabel (substitution S) C.system)

/-- The flattening relation avoids making a choice of proof of determinism. -/
def SystemFlattening {A : RankedSet} {n : ℕ}
    (S : System (System A) n) (T : System A n) : Prop :=
  T.val = flatten (relabel (fun _ U => U.val) S.val)

end Lax369799.Flattening
