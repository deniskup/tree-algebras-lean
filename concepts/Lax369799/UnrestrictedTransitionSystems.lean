import Lax369799.TransitionSystems

/-!
---
title: Arbitrary transition systems and bisimulations
type: definition
---
A pointed transition system may have an arbitrary state space. The usual
back-and-forth definition of bisimulation imposes no finiteness or
reachability assumption. Finite transition systems embed by retaining
their vertices, initial point, edges, and proposition valuations.
-/

namespace Lax369799.UnrestrictedTransitionSystems

structure TransitionSystem (P : Type) where
  Vertex : Type
  initial : Vertex
  edge : Vertex → Vertex → Prop
  valuation : Vertex → Set P

def ofFinite {P : Type} (S : TransitionSystems.TransitionSystem P) : TransitionSystem P :=
  ⟨S.Vertex,S.initial,S.edge,S.valuation⟩

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

end Lax369799.UnrestrictedTransitionSystems

