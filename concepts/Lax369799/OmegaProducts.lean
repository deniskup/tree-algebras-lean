import Lax369799.OmegaDeterminization
import Lax369799.WordFactorization

/-!
---
title: Regular infinite products of linked pairs
type: theorem
---
For a finite monoid, a union of languages V_a(V_e)^ω over linked pairs
ae = a and ee = e is recognized by a deterministic parity word automaton.
Here V_a consists of nonempty words of product a. Increasing cut points
give the nonempty prefix and the successive nonempty blocks explicitly.
-/

namespace Lax369799.OmegaProducts
open UnfoldAutomata WordFactorization

def Accepts {M : Type} [Monoid M] {u : ℕ} (f : Fin u → M)
    (P : M → M → Prop) (w : ℕ → Fin u) : Prop :=
  ∃ (a e : M) (cut : ℕ → ℕ), P a e ∧ e * e = e ∧ a * e = a ∧
    StrictMono cut ∧ 0 < cut 0 ∧ block (f ∘ w) 0 (cut 0) = a ∧
    ∀ i, block (f ∘ w) (cut i) (cut (i + 1)) = e

axiom regular {M : Type} [Monoid M] [Finite M] {u z : ℕ}
    (f : Fin u → M) (P : M → M → Prop) :
    ∃ D : WordCondition u z, ∀ w, D.AcceptsInfinite w ↔ Accepts f P w

end Lax369799.OmegaProducts
