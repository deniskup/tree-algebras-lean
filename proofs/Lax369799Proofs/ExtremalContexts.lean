import Lax369799.ExtremalContexts
import Lax369799Proofs.SetAlgebraTheorems
import Mathlib.Data.Fintype.Sets
import Mathlib.Data.Finite.Prod
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Order.Preorder.Finite

namespace Lax369799Proofs.ExtremalContexts
open Lax369799.RankedSystems Lax369799.SetAlgebras
open Lax369799.AutomatonProperty Lax369799.ExtremalContexts

/--
---
conclusion: Lax369799.ExtremalContexts.delta_deterministic
---
The witness is the flattening of a pattern whose labels are unary
components. Evaluate those components and use associativity.
-/
theorem delta_deterministic {A : RankedSet} (E : SetAlgebra A) {k : ℕ}
    (B : Boundary k) (m : Fin (k + 1) → A 1) (a : A k) :
    Deterministic E (E.eval k (delta B m a)) := by
  refine ⟨relabel E.eval (deltaPattern B m a), ?_, E.associative k (deltaPattern B m a)⟩
  intro v
  refine Fin.cases (Nat.le_refl 1) (fun _ => Nat.le_refl 1) v

/--
---
conclusion: Lax369799.ExtremalContexts.extremal_choice
---
There are finitely many choices of the unary tuple, the hole root mark,
and the loop directions. Choose a minimal accepting datum below the given
one in the product preorder, with boundary inclusions reversed.
-/
theorem extremal_choice {A : RankedSet} (E : SetAlgebra A) (hA : RankwiseFinite A)
    (f : A 0) {k : ℕ} (a : A k) (x : Data A k) (hx : Accepts E f a x) :
    ∃ y : Data A k, DataBelow E y x ∧ Accepts E f a y ∧
      ∀ z : Data A k, DataBelow E z y → Accepts E f a z → DataBelow E y z := by
  classical
  let : Finite (A 1) := hA 1
  let : Finite (Boundary k) := Finite.of_injective (fun B : Boundary k => (B.root, B.loops)) (by
    rintro ⟨r, l⟩ ⟨r', l'⟩ h
    obtain ⟨hr, hl⟩ := Prod.mk.inj h
    cases hr
    cases hl
    rfl)
  obtain ⟨refl, _, trans, _⟩ := Lax369799Proofs.SetAlgebraTheorems.order_laws E 1
  let : Preorder (Data A k) := {
    le := DataBelow E
    le_refl := fun x => ⟨id, Set.Subset.rfl, fun i => refl (x.2 i)⟩
    le_trans := fun x y z hxy hyz => ⟨hxy.1 ∘ hyz.1, hyz.2.1.trans hxy.2.1,
      fun i => trans _ _ _ (hxy.2.2 i) (hyz.2.2 i)⟩ }
  obtain ⟨y, hyx, hy, hmin⟩ := Finite.exists_le_minimal (p := Accepts E f a) hx
  exact ⟨y, hyx, hy, fun z hzy hz => hmin hz hzy⟩

end Lax369799Proofs.ExtremalContexts
