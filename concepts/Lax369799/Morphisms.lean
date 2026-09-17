import Lax369799.RankedSystems

/-!
---
title: Morphisms, unfoldings, and yields
type: definition
---
A morphism preserves labels, initial vertices, root vertices, and edges.
Local surjectivity requires equality of the corresponding images at initial
vertices, roots, and the successors of each vertex. Unfold-equivalence means
having a common locally surjective cover. Initial yields are systems with
an unfolding that maps into the given set-system; root yields are their
planted counterparts after uprooting. See Sections 2.3–2.5.
-/

namespace Lax369799.Morphisms
open RankedSystems

structure Morphism {A : RankedSet} {n : ℕ} (S T : SetSystem A n) where
  toFun : S.Vertex → T.Vertex
  initial : ∀ v, v ∈ S.graph.initial → toFun v ∈ T.graph.initial
  root : ∀ v, v ∈ S.graph.root → toFun v ∈ T.graph.root
  label : ∀ v, T.graph.label (toFun v) = S.graph.label v
  edge : ∀ v d t, S.graph.edge v d t → T.graph.edge (toFun v) d (Sum.map toFun id t)

def Morphism.LocallySurjective {A : RankedSet} {n : ℕ} {S T : SetSystem A n}
    (f : Morphism S T) : Prop :=
  (∀ w ∈ T.graph.initial, ∃ v ∈ S.graph.initial, f.toFun v = w) ∧
  (∀ w ∈ T.graph.root, ∃ v ∈ S.graph.root, f.toFun v = w) ∧
  ∀ v d t, T.graph.edge (f.toFun v) d t →
    ∃ s, S.graph.edge v d s ∧ Sum.map f.toFun id s = t

def Isomorphic {A : RankedSet} {n : ℕ} (S T : SetSystem A n) : Prop :=
  ∃ f : Morphism S T, Function.Bijective f.toFun ∧ f.LocallySurjective

/-- `UnfoldsTo S T` means that T is an unfolding of S. -/
def UnfoldsTo {A : RankedSet} {n : ℕ} (S T : SetSystem A n) : Prop :=
  ∃ f : Morphism T S, f.LocallySurjective

def UnfoldEquivalent {A : RankedSet} {n : ℕ} (S T : SetSystem A n) : Prop :=
  ∃ U : SetSystem A n, UnfoldsTo S U ∧ UnfoldsTo T U

def DirectResolution {A : RankedSet} {n : ℕ} (S : SetSystem A n)
    (T : System A n) : Prop := Nonempty (Morphism T.val S)

def InitYield {A : RankedSet} {n : ℕ} (S : SetSystem A n)
    (T : System A n) : Prop :=
  ∃ D : System A n, DirectResolution S D ∧ UnfoldsTo T.val D.val

def Yield {A : RankedSet} {n : ℕ} (S T : SetSystem A n) : Prop :=
  (∃ U : System A n, InitYield S U ∧ T = U.val) ∨
  (∃ U : System A n, InitYield (uproot S) U ∧ T = plant U.val)

def YieldBelow {A : RankedSet} {n : ℕ} (S T : SetSystem A n) : Prop :=
  ∀ U, Yield S U → Yield T U

def YieldEquivalent {A : RankedSet} {n : ℕ} (S T : SetSystem A n) : Prop :=
  ∀ U, Yield S U ↔ Yield T U

abbrev RegularTree (A : RankedSet) (n : ℕ) :=
  Quot (fun (S T : System A n) => UnfoldEquivalent S.val T.val)

end Lax369799.Morphisms
