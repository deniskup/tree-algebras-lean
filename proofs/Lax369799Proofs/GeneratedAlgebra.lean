import Lax369799.GeneratedAlgebra
import Lax369799Proofs.Flattening

set_option backward.isDefEq.respectTransparency false
namespace Lax369799Proofs.GeneratedAlgebra
open Lax369799.RankedSystems Lax369799.Algebras Lax369799.Morphisms Lax369799.Flattening
open Lax369799.GeneratedAlgebra

noncomputable def representative {A B : RankedSet} (E : Algebra B) (η : RankedMap A B) :
    RankedMap (Carrier E η) (System A) := fun _ b => Classical.choose b.property

theorem representative_value {A B : RankedSet} (E : Algebra B) (η : RankedMap A B)
    (n : ℕ) (b : Carrier E η n) :
    E.eval n (relabelSystem η (representative E η n b)) = b.val :=
  Classical.choose_spec b.property

private theorem realized {A B : RankedSet} (E : Algebra B) (η : RankedMap A B)
    {n : ℕ} (S : System (Carrier E η) n) :
    ∃ T : System A n, E.eval n (relabelSystem η T) = E.eval n (relabelSystem (projection E η) S) := by
  let U := relabelSystem (representative E η) S
  obtain ⟨T, ht⟩ := Flattening.flatten_system U
  let V := relabelSystem (fun k R => relabelSystem η R) U
  have hv : SystemFlattening V (relabelSystem η T) := by
    change relabel η T.val = _
    rw [ht]
    rfl
  have he := E.associative n V (relabelSystem η T) hv
  have hh : (fun k b => E.eval k (relabelSystem η (representative E η k b))) = projection E η := by
    funext k b
    exact representative_value E η k b
  refine ⟨T, ?_⟩
  change E.eval n (relabelSystem (fun k b => E.eval k (relabelSystem η (representative E η k b))) S) = _ at he
  rw [hh] at he
  exact he.symm

private noncomputable def evaluate {A B : RankedSet} (E : Algebra B) (η : RankedMap A B)
    (n : ℕ) (S : System (Carrier E η) n) : Carrier E η n :=
  ⟨E.eval n (relabelSystem (projection E η) S), realized E η S⟩

private def relabelMorphism {A B : RankedSet} (η : RankedMap A B) {n : ℕ}
    {S T : SetSystem A n} (f : Morphism S T) : Morphism (relabel η S) (relabel η T) where
  toFun := f.toFun
  initial := f.initial
  root := f.root
  label := fun v => congrArg (fun a : Symbol A => (⟨a.1, η a.1 a.2⟩ : Symbol B)) (f.label v)
  edge := f.edge

/--
---
conclusion: Lax369799.GeneratedAlgebra.algebra
---
Choose a realizing system for each vertex label and flatten the resulting
system of systems. Associativity proves closure under evaluation. The
inclusion into the original algebra transports all algebra laws.
-/
theorem algebra {A B : RankedSet} (E : Algebra B) (η : RankedMap A B) :
    ∃ G : Algebra (Carrier E η), ∀ n (S : System (Carrier E η) n),
      (G.eval n S).val = E.eval n (relabelSystem (projection E η) S) := by
  refine ⟨{
    eval := evaluate E η
    unit := ?_
    isomorphic := ?_
    associative := ?_ }, fun _ _ => rfl⟩
  · rintro n S T ⟨f, hf, hc⟩
    apply Subtype.ext
    exact E.isomorphic n _ _ ⟨relabelMorphism (projection E η) f, hf, hc⟩
  · intro n a
    apply Subtype.ext
    exact E.unit n a.val
  · intro n S T ht
    apply Subtype.ext
    let U := relabelSystem (fun k R => relabelSystem (projection E η) R) S
    have hu : SystemFlattening U (relabelSystem (projection E η) T) := by
      change relabel (projection E η) T.val = _
      rw [ht]
      rfl
    exact E.associative n U (relabelSystem (projection E η) T) hu

/--
---
conclusion: Lax369799.GeneratedAlgebra.finite_carrier
---
Each generated sort is a subtype of the corresponding finite original sort.
-/
theorem finite_carrier {A B : RankedSet} (E : Algebra B) (η : RankedMap A B)
    (hB : RankwiseFinite B) : RankwiseFinite (Carrier E η) := by
  intro n
  let : Finite (B n) := hB n
  exact Finite.of_injective (fun b : Carrier E η n => b.val) Subtype.val_injective

/--
---
conclusion: Lax369799.GeneratedAlgebra.recognition
---
The projected generated-letter map is the original letter map, and the
subalgebra evaluation commutes with projection. Use the same accepting values.
-/
theorem recognition {A B : RankedSet} (E : Algebra B) (η : RankedMap A B)
    (G : Algebra (Carrier E η))
    (hG : ∀ n (S : System (Carrier E η) n), (G.eval n S).val = E.eval n (relabelSystem (projection E η) S))
    (F : Set (B 0)) (L : Language A) (hL : Recognizes E η F L) :
    Recognizes G (letter E η) {b | b.val ∈ F} L := by
  intro S
  change S ∈ L ↔ (G.eval 0 (relabelSystem (letter E η) S)).val ∈ F
  rw [hG]
  exact hL S

end Lax369799Proofs.GeneratedAlgebra
