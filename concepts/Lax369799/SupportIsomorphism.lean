import Lax369799.SupportEvaluation

/-!
---
title: Isomorphisms and compacted output values
type: theorem
---
Output compaction along a prescribed support map and reflection of
isomorphisms through injective renaming. Isomorphic systems have equal
observation profiles, and injective output renaming preserves equality
of profiles.
-/

namespace Lax369799.SupportIsomorphism
open RankedSystems Morphisms Renaming FinitePresentations

axiom compact_along {A : RankedSet} {m n : ℕ} (S : System A n)
    (σ : Fin m → Fin n) (hσ : Function.Injective σ)
    (hs : ∀ j, (∃ v d, S.val.graph.edge v d (.inr j)) ↔ j ∈ Set.range σ) :
    ∃ T : SupportedSystems.System A m, renameSystem σ T.val = S

axiom reflect_morphism {A : RankedSet} {m n : ℕ} (σ : Fin m → Fin n)
    (hσ : Function.Injective σ) (S T : System A m)
    (f : Morphism (renameSystem σ S).val (renameSystem σ T).val) :
    ∃ g : Morphism S.val T.val, g.toFun = f.toFun

axiom occurs_isomorphic {A : RankedSet} {n : ℕ} (S T : System A n)
    (h : Isomorphic S.val T.val) (j : Fin n) :
    (∃ v d, S.val.graph.edge v d (.inr j)) ↔ ∃ v d, T.val.graph.edge v d (.inr j)

axiom profile_isomorphic {B : RankedSet} (E : SupportedAlgebras.Algebra B) {n : ℕ}
    (S T : System B n) (h : Isomorphic S.val T.val) :
    SupportEvaluation.Equivalent E S T

axiom profile_injective_rename {B : RankedSet} (E : SupportedAlgebras.Algebra B)
    {m n : ℕ} (σ : Fin m → Fin n) (hσ : Function.Injective σ)
    (S T : System B m) (h : SupportEvaluation.Equivalent E S T) :
    SupportEvaluation.Equivalent E (renameSystem σ S) (renameSystem σ T)

end Lax369799.SupportIsomorphism
