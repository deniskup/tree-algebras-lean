import Lax369799.OmegaProducts

/-!
---
title: Recurrent cuts in a linked-pair factorization
type: theorem
---
A linked-pair factorization can be thinned so that every cut visits the
same vertex of a finite graph. Absorption and idempotence preserve the
prefix and block values when successive blocks are grouped.
-/

namespace Lax369799.LinkedPairFactorizations
open WordFactorization OmegaProducts

axiom recurrent_factorization {M V : Type} [Monoid M] [Finite V] {u : ℕ}
    (f : Fin u → M) (P : M → M → Prop) (w : ℕ → Fin u) (v : ℕ → V)
    (h : Accepts f P w) :
    ∃ (a e : M) (c : ℕ → ℕ) (r : V), P a e ∧ e * e = e ∧ a * e = a ∧
      StrictMono c ∧ 0 < c 0 ∧ (∀ i, v (c i) = r) ∧
      (∀ i, block (f ∘ w) 0 (c i) = a) ∧
      (∀ i j, i < j → block (f ∘ w) (c i) (c j) = e)

end Lax369799.LinkedPairFactorizations
