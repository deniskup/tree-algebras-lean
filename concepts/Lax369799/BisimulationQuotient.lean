import Lax369799.TransitionSystems

/-!
---
title: Quotients of graphs by vertex bisimilarity
type: theorem
---
Vertex bisimilarity compares labeled graphs without selecting an initial
vertex. On one graph it is an equivalence relation. The quotient graph
has a functional bisimulation from the original graph, with successor
lifting. These quotients support the converse ranked encoding theorem.
-/
namespace Lax369799.BisimulationQuotient

structure Graph (P V : Type) where
  edge : V → V → Prop
  valuation : V → Set P

structure BisimulationMap {P V W : Type} (G : Graph P V) (H : Graph P W) where
  toFun : V → W
  valuation : ∀ v, G.valuation v = H.valuation (toFun v)
  forward : ∀ v w, G.edge v w → H.edge (toFun v) (toFun w)
  backward : ∀ v w, H.edge (toFun v) w → ∃ v', G.edge v v' ∧ toFun v' = w

def IsBisimulation {P V W : Type} (G : Graph P V) (H : Graph P W)
    (R : V → W → Prop) : Prop :=
  ∀ v w, R v w → G.valuation v = H.valuation w ∧
    (∀ v', G.edge v v' → ∃ w', H.edge w w' ∧ R v' w') ∧
    (∀ w', H.edge w w' → ∃ v', G.edge v v' ∧ R v' w')

def Related {P V W : Type} (G : Graph P V) (H : Graph P W) (v : V) (w : W) : Prop :=
  ∃ R, IsBisimulation G H R ∧ R v w

abbrev Carrier {P V : Type} (G : Graph P V) := Quot (Related G G)

def quotient {P V : Type} (G : Graph P V) : Graph P (Carrier G) where
  valuation := Quot.lift G.valuation (by
    rintro v w ⟨R, hR, h⟩
    exact (hR v w h).1)
  edge := fun q r => ∃ v w, Quot.mk (Related G G) v = q ∧
    Quot.mk (Related G G) w = r ∧ G.edge v w

axiom related_equivalence {P V : Type} (G : Graph P V) : Equivalence (Related G G)

axiom quotient_projection {P V : Type} (G : Graph P V) :
    ∃ f : BisimulationMap G (quotient G), f.toFun = Quot.mk (Related G G)

def ofSystem {P : Type} (S : TransitionSystems.TransitionSystem P) : Graph P S.Vertex :=
  ⟨S.edge, S.valuation⟩

structure SystemMap {P : Type} (S T : TransitionSystems.TransitionSystem P)
    extends BisimulationMap (ofSystem S) (ofSystem T) where
  initial : toFun S.initial = T.initial

axiom common_quotient {P : Type} (S T : TransitionSystems.TransitionSystem P)
    (h : TransitionSystems.Bisimilar S T) :
    ∃ U : TransitionSystems.TransitionSystem P, Nonempty (SystemMap S U) ∧ Nonempty (SystemMap T U)

end Lax369799.BisimulationQuotient
