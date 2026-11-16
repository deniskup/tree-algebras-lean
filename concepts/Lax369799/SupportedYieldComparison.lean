import Lax369799.SupportedYields
import Lax369799.FiniteYieldContinuity

/-!
---
title: Supported yields, contextual order, and substitution congruence
type: theorem
---
Yields with explicit variable maps agree with the reachable presentation
interface after unused outputs are compacted. The comparison preserves
both initial and root yields. Yield inclusion is stable under contexts
and simultaneous substitution, and reverses the yield-syntactic order.
-/

namespace Lax369799.SupportedYieldComparison
open RankedSystems FinitePresentations FiniteContexts
open SupportedMorphisms FiniteRenaming SupportedYields

axiom initial_yield {A : RankedSet} {m n : ℕ} (S : FiniteSystem A n)
    (U : SupportedSystems.System A m) (σ : Fin m → Fin n) :
    InitialYield S U σ ↔ Morphisms.InitYield (trim S.graph) (Renaming.renameSystem σ U.val)

axiom root_yield {A : RankedSet} {m n : ℕ} (S : FiniteSystem A n)
    (U : SupportedSystems.System A m) (σ : Fin m → Fin n) :
    RootYield S U σ ↔ Morphisms.InitYield (RankedSystems.uproot (trim S.graph)) (Renaming.renameSystem σ U.val)

axiom legacy_below {A : RankedSet} {n : ℕ} (S T : FiniteSystem A n) :
    YieldBelow S T ↔ Morphisms.YieldBelow (trim S.graph) (trim T.graph)

axiom context_mono {A : RankedSet} {k n : ℕ} (C : Context A k n)
    (S T : FiniteSystem A k) (h : YieldBelow S T) : YieldBelow (plug C S) (plug C T)

axiom yield_order {A : RankedSet} (L : Algebras.Language A) {n : ℕ}
    (S T : FiniteSystem A n) (h : YieldBelow S T) :
    FiniteContextualOrder.Below (FiniteAcceptance.Accepting L) T S

axiom flatten_mono {A : RankedSet} {n : ℕ} (P : FiniteSystem (FiniteSystem A) n)
    (Q : ∀ v, FiniteSystem A (P.graph.label v).1) (h : ∀ v, YieldBelow (Inner P.graph v) (Q v)) :
    YieldBelow (flatten P) (flatten (withLabels P Q))

axiom flatten_congruence {A : RankedSet} {n : ℕ} (P : FiniteSystem (FiniteSystem A) n)
    (Q : ∀ v, FiniteSystem A (P.graph.label v).1) (h : ∀ v, YieldEquivalent (Inner P.graph v) (Q v)) :
    YieldEquivalent (flatten P) (flatten (withLabels P Q))

end Lax369799.SupportedYieldComparison
