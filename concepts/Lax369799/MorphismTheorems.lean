import Lax369799.Morphisms

/-!
---
title: Morphism and yield theorems
type: theorem
---
The structural results of Sections 2.3–2.5: composition and pullbacks of
morphisms, stability of local surjectivity, equivalence of unfoldings,
and preservation of yields. The pullback includes its universal property
and the local-surjectivity conclusions for both projections.
-/

namespace Lax369799.MorphismTheorems
open RankedSystems Morphisms

axiom composition {A : RankedSet} {n : ℕ} {S T U : SetSystem A n}
    (f : Morphism S T) (g : Morphism T U) :
    ∃ h : Morphism S U, h.toFun = g.toFun ∘ f.toFun ∧
      (f.LocallySurjective → g.LocallySurjective → h.LocallySurjective)

axiom pullback {A : RankedSet} {n : ℕ} {S T U : SetSystem A n}
    (f : Morphism S U) (g : Morphism T U) :
    ∃ (P : SetSystem A n) (p : Morphism P S) (q : Morphism P T),
      f.toFun ∘ p.toFun = g.toFun ∘ q.toFun ∧
      (∀ (V : SetSystem A n) (a : Morphism V S) (b : Morphism V T),
        f.toFun ∘ a.toFun = g.toFun ∘ b.toFun →
        ∃! h : Morphism V P, p.toFun ∘ h.toFun = a.toFun ∧ q.toFun ∘ h.toFun = b.toFun) ∧
      (f.LocallySurjective → q.LocallySurjective) ∧
      (g.LocallySurjective → p.LocallySurjective)

axiom unfold_equivalence (A : RankedSet) (n : ℕ) :
  Equivalence (@UnfoldEquivalent A n)

axiom system_morphism_locally_surjective {A : RankedSet} {n : ℕ}
    (S T : System A n) (f : Morphism S.val T.val) : f.LocallySurjective

axiom morphism_yields {A : RankedSet} {n : ℕ} {S T : SetSystem A n}
    (f : Morphism S T) : YieldBelow S T ∧ (f.LocallySurjective → YieldEquivalent S T)

axiom system_yield_equivalence {A : RankedSet} {n : ℕ} (S T : System A n) :
  UnfoldEquivalent S.val T.val ↔ YieldEquivalent S.val T.val

end Lax369799.MorphismTheorems
