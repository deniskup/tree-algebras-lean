import Lax369799.FiniteMorphisms

/-!
---
title: Composition and pullbacks without reachability pruning
type: theorem
---
The morphisms of revised Definition 8 retain every vertex. Local
surjectivity and surjectivity on vertices are separate requirements.
Lemmas 9 and 14 hold for these presentations, including the folding
clauses and the full pullback universal property.
-/

namespace Lax369799.FiniteStructureTheorems
open RankedSystems FinitePresentations FiniteMorphisms

def LocallySurjective {A : RankedSet} {n : ℕ} {S T : FiniteSystem A n}
    (f : Morphism S T) : Prop :=
  (∀ w, T.graph.initial w → ∃ v, S.graph.initial v ∧ f.toFun v = w) ∧
  (∀ w, T.graph.root w → ∃ v, S.graph.root v ∧ f.toFun v = w) ∧
  ∀ v d t, T.graph.edge (f.toFun v) d t →
    ∃ s, S.graph.edge v d s ∧ Sum.map f.toFun id s = t

def Folding {A : RankedSet} {n : ℕ} {S T : FiniteSystem A n}
    (f : Morphism S T) : Prop := LocallySurjective f ∧ Function.Surjective f.toFun

def UnfoldEquivalent {A : RankedSet} {n : ℕ} (S T : FiniteSystem A n) : Prop :=
  ∃ (U : FiniteSystem A n) (f : Morphism U S) (g : Morphism U T), Folding f ∧ Folding g

axiom composition {A : RankedSet} {n : ℕ} {S T U : FiniteSystem A n}
    (f : Morphism S T) (g : Morphism T U) :
    ∃ h : Morphism S U, h.toFun = g.toFun ∘ f.toFun ∧
      (LocallySurjective f → LocallySurjective g → LocallySurjective h) ∧
      (Folding f → Folding g → Folding h)

axiom pullback {A : RankedSet} {n : ℕ} {S T U : FiniteSystem A n}
    (f : Morphism S U) (g : Morphism T U) :
    ∃ (P : FiniteSystem A n) (p : Morphism P S) (q : Morphism P T),
      f.toFun ∘ p.toFun = g.toFun ∘ q.toFun ∧
      (∀ (V : FiniteSystem A n) (a : Morphism V S) (b : Morphism V T),
        f.toFun ∘ a.toFun = g.toFun ∘ b.toFun →
        ∃! h : Morphism V P, p.toFun ∘ h.toFun = a.toFun ∧ q.toFun ∘ h.toFun = b.toFun) ∧
      (LocallySurjective f → LocallySurjective q) ∧
      (LocallySurjective g → LocallySurjective p) ∧
      (Folding f → Folding q) ∧ (Folding g → Folding p)

axiom unfold_equivalence (A : RankedSet) (n : ℕ) :
    Equivalence (@UnfoldEquivalent A n)

end Lax369799.FiniteStructureTheorems
