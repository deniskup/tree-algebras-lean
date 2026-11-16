import Lax369799.SupportedSystems
import Lax369799.FiniteStructureTheorems
import Lax369799.ResolutionLifting

/-!
---
title: Selection and common unfoldings of fully supported systems
type: theorem
---
Morphisms between revised systems are foldings. A locally surjective
morphism from an unpruned set-system to a system admits an injective
system selection (Lemma 11). Common unfoldings can be chosen to be
systems (Lemma 20), and unfoldings lift through surjective renaming
while preserving full support (Lemma 24).
-/

namespace Lax369799.SupportedMorphisms
open RankedSystems (RankedSet)
open FinitePresentations FiniteMorphisms FiniteStructureTheorems

def presentation {A : RankedSet} {n : ℕ} (S : SupportedSystems.System A n) : FiniteSystem A n :=
  ofSetSystem S.val.val

axiom source_support {A : RankedSet} {n : ℕ}
    (S : RankedSystems.System A n) (T : SupportedSystems.System A n)
    (f : Morphism (ofSetSystem S.val) (presentation T)) : SupportedSystems.FullySupported S

axiom system_folding {A : RankedSet} {n : ℕ} (S T : SupportedSystems.System A n)
    (f : Morphism (presentation S) (presentation T)) : Folding f

axiom system_selection {A : RankedSet} {n : ℕ} (S : FiniteSystem A n)
    (T : SupportedSystems.System A n) (f : Morphism S (presentation T))
    (hf : LocallySurjective f) :
    ∃ (U : SupportedSystems.System A n) (i : Morphism (presentation U) S)
      (g : Morphism (presentation U) (presentation T)),
      Function.Injective i.toFun ∧ g.toFun = f.toFun ∘ i.toFun ∧ Folding g

axiom common_system_unfolding {A : RankedSet} {n : ℕ}
    (S T : SupportedSystems.System A n)
    (h : UnfoldEquivalent (presentation S) (presentation T)) :
    ∃ (U : SupportedSystems.System A n) (f : Morphism (presentation U) (presentation S))
      (g : Morphism (presentation U) (presentation T)), Folding f ∧ Folding g

axiom system_pullback {A : RankedSet} {n : ℕ} (S T U : SupportedSystems.System A n)
    (f : Morphism (presentation S) (presentation U))
    (g : Morphism (presentation T) (presentation U)) :
    ∃ (P : SupportedSystems.System A n) (p : Morphism (presentation P) (presentation S))
      (q : Morphism (presentation P) (presentation T)),
      f.toFun ∘ p.toFun = g.toFun ∘ q.toFun ∧ Folding p ∧ Folding q ∧
      (∀ (V : SupportedSystems.System A n) (a : Morphism (presentation V) (presentation S))
        (b : Morphism (presentation V) (presentation T)),
        f.toFun ∘ a.toFun = g.toFun ∘ b.toFun →
        ∃! h : Morphism (presentation V) (presentation P),
          p.toFun ∘ h.toFun = a.toFun ∧ q.toFun ∘ h.toFun = b.toFun)

axiom rename_lift {A : RankedSet} {m n : ℕ} (σ : Fin m → Fin n)
    (hσ : Function.Surjective σ) (S : SupportedSystems.System A m)
    (R : SupportedSystems.System A n)
    (f : Morphisms.Morphism R.val.val (Resolutions.rename σ S.val.val)) :
    ∃ U : SupportedSystems.System A m,
      SupportedSystems.rename σ hσ U = R ∧ Morphisms.UnfoldsTo S.val.val U.val.val

end Lax369799.SupportedMorphisms
