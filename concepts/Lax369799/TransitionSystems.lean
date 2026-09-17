import Lax369799.RankedSystems

/-!
---
title: Finite transition systems and bisimulation
type: definition
---
A finite transition system is a finite directed graph with an initial vertex
and a valuation of proposition letters at each vertex. All vertices are
reachable from the initial vertex. A bisimulation relates the initial
vertices, preserves valuations, and matches successors in both directions.
This is the usual bisimulation of Section 6.1, without an ordering or
multiplicity on the successors.
-/

namespace Lax369799.TransitionSystems

structure TransitionSystem (P : Type) where
  size : ℕ
  initial : Fin size
  edge : Fin size → Fin size → Prop
  valuation : Fin size → Set P
  reachable : ∀ v, Relation.ReflTransGen edge initial v

abbrev TransitionSystem.Vertex {P : Type} (S : TransitionSystem P) := Fin S.size

def Bisimulation {P : Type} (S T : TransitionSystem P)
    (R : S.Vertex → T.Vertex → Prop) : Prop :=
  R S.initial T.initial ∧ ∀ v w, R v w →
    S.valuation v = T.valuation w ∧
    (∀ v', S.edge v v' → ∃ w', T.edge w w' ∧ R v' w') ∧
    (∀ w', T.edge w w' → ∃ v', S.edge v v' ∧ R v' w')

def Bisimilar {P : Type} (S T : TransitionSystem P) : Prop :=
  ∃ R, Bisimulation S T R

def BisimulationInvariant {P : Type} (L : Set (TransitionSystem P)) : Prop :=
  ∀ S T, Bisimilar S T → (S ∈ L ↔ T ∈ L)

end Lax369799.TransitionSystems
