import Lax369799.ExpandedSyntacticAlgebra

/-!
---
title: Acceptance from finite families of covering components
type: theorem
---
A finite family of presentation maps jointly covers a target if it covers
all vertices and marks and lifts every successor at each source vertex.
Acceptance of the components implies acceptance of the target.
-/
namespace Lax369799.FiniteCoverFamilies
open RankedSystems (RankedSet)
open FinitePresentations FiniteSyntacticAlgebra FiniteContextualOrder FiniteAcceptance
open ExpandedSyntacticAlgebra

structure JointCover {A : RankedSet} {m : ℕ} (T : Fin m → FiniteSystem A 0)
    (P : FiniteSystem A 0) where
  map : ∀ i, FiniteMorphisms.Morphism (T i) P
  edges : ∀ i v d t, P.graph.edge ((map i).toFun v) d t →
    ∃ s, (T i).graph.edge v d s ∧ Sum.map (map i).toFun id s = t
  vertices : ∀ v : P.Vertex, ∃ i w, (map i).toFun w = v
  initials : ∀ v, v ∈ P.graph.initial → ∃ i w, w ∈ (T i).graph.initial ∧ (map i).toFun w = v
  roots : ∀ v, v ∈ P.graph.root → ∃ i w, w ∈ (T i).graph.root ∧ (map i).toFun w = v


axiom acceptance {A : RankedSet} (L : Algebras.Language A)
    [Finite (Carrier (Accepting L) 0)] (E : SyntacticAlgebra L)
    {m : ℕ} (hm : 0 < m) (T : Fin m → FiniteSystem (Carrier (Accepting L)) 0)
    (P : FiniteSystem (Carrier (Accepting L)) 0) (F : JointCover T P)
    (hT : ∀ i, AcceptingClass (Accepting L) (E.algebra.eval 0 (T i))) :
    AcceptingClass (Accepting L) (E.algebra.eval 0 P)

end Lax369799.FiniteCoverFamilies
