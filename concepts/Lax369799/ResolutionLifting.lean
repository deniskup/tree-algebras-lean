import Lax369799.Renaming

/-!
---
title: Lifting unfoldings through variable renaming
type: theorem
---
A morphism into a renamed system can be lifted by restoring the variable
names dictated by the original system. Renaming the lifted system gives
back the source exactly. This preserves variable origins when passing
from direct resolutions to resolutions.
-/
namespace Lax369799.ResolutionLifting
open RankedSystems Morphisms Resolutions

axiom rename_lift {A : RankedSet} {m n : ℕ} (σ : Fin m → Fin n)
    (S : System A m) (R : System A n) (f : Morphism R.val (rename σ S.val)) :
    ∃ U : System A m, rename σ U.val = R.val ∧ UnfoldsTo S.val U.val

/-- Yield inclusion transfers resolutions while preserving the variable map. -/
axiom transfer {A : RankedSet} {m n : ℕ} {S S' : SetSystem A n}
    (h : YieldBelow S S') (T : System A m) (σ : Fin m → Fin n)
    (hT : IsResolution S T σ) :
    ∃ T' : System A m, IsResolution S' T' σ ∧ UnfoldsTo T.val T'.val

end Lax369799.ResolutionLifting
