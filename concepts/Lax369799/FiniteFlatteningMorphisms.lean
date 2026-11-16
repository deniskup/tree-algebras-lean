import Lax369799.FiniteStructureTheorems

/-!
---
title: Unpruned substitution preserves morphisms and unfold-equivalence
type: theorem
---
Lemmas 34 and 35 and their congruence consequences (Lemmas 39 and 40),
with all vertices retained. The outer lifting uses global surjectivity
to cover roots belonging to labels at unreachable outer vertices.
-/

namespace Lax369799.FiniteFlatteningMorphisms
open RankedSystems FinitePresentations FiniteMorphisms FiniteStructureTheorems

axiom inner {A : RankedSet} {n : ℕ} (P : FiniteSystem (FiniteSystem A) n)
    (Q : ∀ v, FiniteSystem A (P.graph.label v).1)
    (f : ∀ v, Morphism (Inner P.graph v) (Q v)) :
    ∃ g : Morphism (flatten P) (flatten (withLabels P Q)),
      ((∀ v, LocallySurjective (f v)) → LocallySurjective g) ∧
      ((∀ v, Folding (f v)) → Folding g)

axiom outer {A : RankedSet} {n : ℕ} {S T : FiniteSystem (FiniteSystem A) n}
    (f : Morphism S T) :
    ∃ g : Morphism (flatten S) (flatten T), Folding f → Folding g

axiom outer_congruence {A : RankedSet} {n : ℕ} (S T : FiniteSystem (FiniteSystem A) n)
    (h : UnfoldEquivalent S T) : UnfoldEquivalent (flatten S) (flatten T)

axiom inner_congruence {A : RankedSet} {n : ℕ} (P : FiniteSystem (FiniteSystem A) n)
    (Q : ∀ v, FiniteSystem A (P.graph.label v).1)
    (h : ∀ v, UnfoldEquivalent (Inner P.graph v) (Q v)) :
    UnfoldEquivalent (flatten P) (flatten (withLabels P Q))

end Lax369799.FiniteFlatteningMorphisms
