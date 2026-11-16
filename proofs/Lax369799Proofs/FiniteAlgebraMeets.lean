import Lax369799.FiniteAlgebraMeets
import Lax369799Proofs.SetSystemAlgebras

namespace Lax369799Proofs.FiniteAlgebraMeets
set_option backward.isDefEq.respectTransparency false
open Lax369799
open RankedSystems (RankedSet)
open FinitePresentations SetSystemAlgebras FiniteAlgebraMeets

private def pick {A : RankedSet} {n k : ℕ} (f : Fin k → A n) (i : Fin k) :
    FiniteMorphisms.Morphism (atomic (f i)) (family f) where
  toFun := fun _ => i
  initial := fun _ _ => True.intro
  root := fun _ => False.elim
  label := fun _ => rfl
  edge := by rintro v d t ⟨j, rfl, rfl⟩; exact ⟨j, rfl, rfl⟩

private def collapse {A : RankedSet} {n k : ℕ} (x : A n) :
    FiniteMorphisms.Morphism (family (fun _ : Fin k => x)) (atomic x) where
  toFun := fun _ => (0 : Fin 1)
  initial := fun _ _ => True.intro
  root := fun _ => False.elim
  label := fun _ => rfl
  edge := by rintro v d t ⟨j, rfl, rfl⟩; exact ⟨j, rfl, rfl⟩

/--
---
conclusion: Lax369799.FiniteAlgebraMeets.component
---
The atomic inclusion into the family gives the reverse comparison of
their evaluations.
-/
theorem component {A : RankedSet} (E : SetAlgebra A) {n k : ℕ}
    (f : Fin k → A n) (i : Fin k) : Below E (value E f) (f i) := by
  have h := E.morphism n (atomic (f i)) (family f) ⟨pick f i⟩
  change Below E (value E f) (E.eval n (atomic (f i))) at h
  rwa [E.unit] at h

/--
---
conclusion: Lax369799.FiniteAlgebraMeets.lower_iff
---
Collapse a constant-labelled family onto its atom, then increase each
label to the corresponding family element. Transitivity gives the
greatest-lower-bound property, also for an empty family.
-/
theorem lower_iff {A : RankedSet} (E : SetAlgebra A) {n k : ℕ}
    (f : Fin k → A n) (x : A n) : Below E x (value E f) ↔ ∀ i, Below E x (f i) := by
  have trans := (SetSystemAlgebras.order_laws E n).2.2.1
  constructor
  · intro h i
    exact trans _ _ _ h (component E f i)
  · intro h
    have hx := E.morphism n (family (fun _ : Fin k => x)) (atomic x) ⟨collapse x⟩
    change Below E (E.eval n (atomic x)) (value E (fun _ : Fin k => x)) at hx
    rw [E.unit] at hx
    have hm := SetSystemAlgebras.evaluation_monotone E (family f) (fun _ => x) f h
    change Below E (value E (fun _ : Fin k => x)) (value E f) at hm
    exact trans _ _ _ hx hm

/--
---
conclusion: Lax369799.FiniteAlgebraMeets.monotone
---
Compare the two families component by component using the universal
property of their meets.
-/
theorem monotone {A : RankedSet} (E : SetAlgebra A) {n k : ℕ}
    (f g : Fin k → A n) (h : ∀ i, Below E (f i) (g i)) : Below E (value E f) (value E g) := by
  apply (lower_iff E g _).mpr
  intro i
  exact (SetSystemAlgebras.order_laws E n).2.2.1 _ _ _ (component E f i) (h i)

end Lax369799Proofs.FiniteAlgebraMeets
