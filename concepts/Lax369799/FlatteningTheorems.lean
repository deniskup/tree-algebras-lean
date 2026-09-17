import Lax369799.Resolutions

/-!
---
title: Flattening, resolutions, and yield congruence
type: theorem
---
Flattening preserves systems. Flatten-resolutions give direct resolutions
of a flattening; conversely, every direct resolution has an unfolding
obtained by flattening a flatten-resolution. Yield inclusion is preserved
by substitution into contexts. These are the central compositional results
of Sections 2.6–2.9.
-/

namespace Lax369799.FlatteningTheorems
open RankedSystems Morphisms Flattening Resolutions

axiom flatten_system {A : RankedSet} {n : ℕ} (S : System (System A) n) :
  ∃ T : System A n, SystemFlattening S T

axiom flatten_resolution_sound {A : RankedSet} {n : ℕ}
    (S : SetSystem (SetSystem A) n) (T : System (System A) n)
    (h : FlattenResolution S T) (U : System A n) (hU : SystemFlattening T U) :
    DirectResolution (flatten S) U

axiom resolution_to_flatten_resolution {A : RankedSet} {n : ℕ}
    (S : SetSystem (SetSystem A) n) (R : System A n)
    (hR : DirectResolution (flatten S) R) :
    ∃ (T : System (System A) n) (U : System A n),
      Nonempty (FlattenResolution S T) ∧ SystemFlattening T U ∧ UnfoldsTo R.val U.val

axiom yield_context_congruence {A : RankedSet} {k n : ℕ}
    (C : SetContext A k n) (S T : SetSystem A k) (h : YieldBelow S T) :
    YieldBelow (plug C S) (plug C T)

axiom unfold_context_congruence {A : RankedSet} {k n : ℕ}
    (C : SetContext A k n) (S T : SetSystem A k) (h : UnfoldEquivalent S T) :
    UnfoldEquivalent (plug C S) (plug C T)

end Lax369799.FlatteningTheorems
