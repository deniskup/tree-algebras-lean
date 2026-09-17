import Lax369799.SetAlgebraTheorems

namespace Lax369799Proofs.SetAlgebraTheorems
open Lax369799.RankedSystems Lax369799.SetAlgebras Lax369799.AutomatonProperty

/--
---
conclusion: Lax369799.SetAlgebraTheorems.low_rank_deterministic
---
The atomic system of a letter of rank at most one is a witnessing system.
-/
theorem low_rank_deterministic {A : RankedSet} (E : SetAlgebra A)
    {n : ℕ} (hn : n ≤ 1) (a : A n) : Deterministic E a :=
  ⟨atomic a, fun _ => hn, E.unit n a⟩

/--
---
conclusion: Lax369799.SetAlgebraTheorems.order_laws
assumptions:
  - Lax369799.SetAlgebraTheorems.meet_laws
---
The associative, commutative, idempotent operation defines its usual
semilattice order.
-/
theorem order_laws {A : RankedSet} (E : SetAlgebra A) (n : ℕ) :
    (∀ a : A n, Below E a a) ∧
    (∀ a b : A n, Below E a b → Below E b a → a = b) ∧
    (∀ a b c : A n, Below E a b → Below E b c → Below E a c) ∧
    (∀ a b c : A n, Below E c (meet E a b) ↔ Below E c a ∧ Below E c b) := by
  obtain ⟨assoc, comm, idem⟩ := Lax369799.SetAlgebraTheorems.meet_laws E n
  change (∀ a, meet E a a = a) ∧
    (∀ a b, meet E a b = a → meet E b a = b → a = b) ∧
    (∀ a b c, meet E a b = a → meet E b c = b → meet E a c = a) ∧
    (∀ a b c, meet E c (meet E a b) = c ↔ meet E c a = c ∧ meet E c b = c)
  have trans : ∀ a b c : A n, meet E a b = a → meet E b c = b → meet E a c = a := by
    intro a b c hab hbc
    calc
      meet E a c = meet E (meet E a b) c := by rw [hab]
      _ = meet E a (meet E b c) := assoc a b c
      _ = a := by rw [hbc, hab]
  refine ⟨idem, ?_, trans, ?_⟩
  · intro a b hab hba
    exact hab.symm.trans ((comm a b).trans hba)
  · intro a b c
    constructor
    · intro h
      constructor
      · apply trans c (meet E a b) a h
        rw [comm a b, assoc b a a, idem, comm]
      · apply trans c (meet E a b) b h
        rw [assoc, idem]
    · rintro ⟨ha, hb⟩
      rw [← assoc, ha, hb]

end Lax369799Proofs.SetAlgebraTheorems
