import Lax369799.FiniteStructureTheorems

/-!
---
title: Variable renaming and inverse renaming without pruning
type: theorem
---
Direct images and inverse images of variable edges retain all vertices.
Their adjunction is Lemma 17 of the revised manuscript. Both operations
preserve morphisms, local surjectivity, and foldings.
-/

namespace Lax369799.FiniteRenaming
open RankedSystems FinitePresentations FiniteMorphisms FiniteStructureTheorems

def push {A : RankedSet} {m n : ℕ} (σ : Fin m → Fin n) (S : FiniteSystem A m) :
    FiniteSystem A n where
  size := S.size
  graph := {
    label := S.graph.label, initial := S.graph.initial, root := S.graph.root
    edge := fun v d t => ∃ s, S.graph.edge v d s ∧ t = Sum.map id σ s
    direction_valid := by rintro v d t ⟨s,hs,_⟩; exact S.graph.direction_valid v d s hs }

def pull {A : RankedSet} {m n : ℕ} (σ : Fin m → Fin n) (S : FiniteSystem A n) :
    FiniteSystem A m where
  size := S.size
  graph := {
    label := S.graph.label, initial := S.graph.initial, root := S.graph.root
    edge := fun v d t => S.graph.edge v d (Sum.map id σ t)
    direction_valid := fun v d _t h => S.graph.direction_valid v d _ h }

axiom adjunction {A : RankedSet} {m n : ℕ} (σ : Fin m → Fin n)
    (S : FiniteSystem A m) (T : FiniteSystem A n) (ρ : S.Vertex → T.Vertex) :
    (∃ f : Morphism (push σ S) T, f.toFun = ρ) ↔
      (∃ g : Morphism S (pull σ T), g.toFun = ρ)

axiom push_morphism {A : RankedSet} {m n : ℕ} (σ : Fin m → Fin n)
    {S T : FiniteSystem A m} (f : Morphism S T) :
    ∃ g : Morphism (push σ S) (push σ T), g.toFun = f.toFun ∧
      (LocallySurjective f → LocallySurjective g) ∧ (Folding f → Folding g)

axiom pull_morphism {A : RankedSet} {m n : ℕ} (σ : Fin m → Fin n)
    {S T : FiniteSystem A n} (f : Morphism S T) :
    ∃ g : Morphism (pull σ S) (pull σ T), g.toFun = f.toFun ∧
      (LocallySurjective f → LocallySurjective g) ∧ (Folding f → Folding g)

axiom pull_flatten {A : RankedSet} {m n : ℕ} (σ : Fin m → Fin n)
    (P : FiniteSystem (FiniteSystem A) n) : pull σ (flatten P) = flatten (pull σ P)

end Lax369799.FiniteRenaming
