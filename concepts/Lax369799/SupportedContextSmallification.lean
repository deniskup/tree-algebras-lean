import Lax369799.SupportedAlgebras
import Lax369799.ContextPorts

/-!
---
title: Smallification in supported contexts
type: theorem
---
Lemma 81 with the original supported algebra and bound |B₀| + |B₁| + 1.
The quotient map is surjective and its section is injective. The new
argument is the surjective renaming of the original system; its context
has precisely the selected hole directions and is trimmed to reachable
vertices. The two closed evaluations agree.
-/

namespace Lax369799.SupportedContextSmallification
open RankedSystems Flattening

axiom smallification {A B : RankedSet} (E : SupportedAlgebras.Algebra B)
    (hB : RankwiseFinite B) (hE : SupportedAlgebras.UnfoldInvariant E) (η : RankedMap A B)
    {m n : ℕ} (C : SetContext A m 0) (hC : C.system.Deterministic)
    (S : SupportedSystems.System A m) (σ : Fin m → Fin n) :
    ∃ (m' : ℕ) (τ : Fin m → Fin m') (sectionMap : Fin m' → Fin m),
      m' ≤ m ∧ Function.Surjective τ ∧ Function.Injective sectionMap ∧
      (∀ j,τ (sectionMap j) = j) ∧ (∀ i,σ (sectionMap (τ i)) = σ i) ∧
      Resolutions.SmallMap B (σ ∘ sectionMap) ∧
      ∃ (S' : SupportedSystems.System A m') (D : SetContext A m' 0),
        S'.val = Renaming.renameSystem τ S.val ∧
        D.system = trim (Lax369799.ContextPorts.resizeGraph C sectionMap) ∧ D.system.Deterministic ∧
        ∃ U V : SupportedSystems.System A 0,
          U.val.val = plug C S.val.val ∧ V.val.val = plug D S'.val.val ∧
          E.eval 0 (SupportedSystems.relabel η U) = E.eval 0 (SupportedSystems.relabel η V)

end Lax369799.SupportedContextSmallification
