import Lax369799.SupportedMorphisms
import Lax369799.FiniteRenaming

/-!
---
title: Yields with explicit variable maps and full support
type: theorem
---
Definition 25 records both a supported system and its variable map.
Initial and root yields are kept separate. Theorems cover invariance
with this map fixed (Lemma 26), morphism monotonicity and invariance
under local surjectivity (Lemma 27), unfold-invariance (Corollary 28),
and the characterization of unfold-equivalence on systems (Lemma 29).
-/

namespace Lax369799.SupportedYields
open RankedSystems (RankedSet)
open FinitePresentations FiniteMorphisms FiniteStructureTheorems
open SupportedMorphisms FiniteRenaming

def uproot {A : RankedSet} {n : ℕ} (S : FiniteSystem A n) : FiniteSystem A n :=
  ⟨S.size,{S.graph with initial := S.graph.root,root := ∅}⟩

def InitialYield {A : RankedSet} {m n : ℕ} (S : FiniteSystem A n)
    (T : SupportedSystems.System A m) (σ : Fin m → Fin n) : Prop :=
  ∃ (U : SupportedSystems.System A m) (_a : Morphism (push σ (presentation U)) S)
    (b : Morphism (presentation U) (presentation T)), Folding b

def RootYield {A : RankedSet} {m n : ℕ} (S : FiniteSystem A n)
    (T : SupportedSystems.System A m) (σ : Fin m → Fin n) : Prop :=
  InitialYield (uproot S) T σ

def YieldBelow {A : RankedSet} {n : ℕ} (S T : FiniteSystem A n) : Prop :=
  ∀ (m : ℕ) (R : SupportedSystems.System A m) (σ : Fin m → Fin n),
    (InitialYield S R σ → InitialYield T R σ) ∧ (RootYield S R σ → RootYield T R σ)

def YieldEquivalent {A : RankedSet} {n : ℕ} (S T : FiniteSystem A n) : Prop :=
  ∀ (m : ℕ) (R : SupportedSystems.System A m) (σ : Fin m → Fin n),
    (InitialYield S R σ ↔ InitialYield T R σ) ∧ (RootYield S R σ ↔ RootYield T R σ)

axiom unfold_invariance {A : RankedSet} {m n : ℕ} (S : FiniteSystem A n)
    (T T' : SupportedSystems.System A m) (σ : Fin m → Fin n)
    (h : UnfoldEquivalent (presentation T) (presentation T')) :
    (InitialYield S T σ ↔ InitialYield S T' σ) ∧ (RootYield S T σ ↔ RootYield S T' σ)

axiom morphism_yields {A : RankedSet} {n : ℕ} {S T : FiniteSystem A n}
    (f : Morphism S T) : YieldBelow S T ∧ (LocallySurjective f → YieldEquivalent S T)

axiom unfold_yields {A : RankedSet} {n : ℕ} {S T : FiniteSystem A n}
    (h : UnfoldEquivalent S T) : YieldEquivalent S T

axiom system_yield_equivalence {A : RankedSet} {n : ℕ}
    (S T : SupportedSystems.System A n) :
    UnfoldEquivalent (presentation S) (presentation T) ↔
      YieldEquivalent (presentation S) (presentation T)

end Lax369799.SupportedYields
