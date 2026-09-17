import Lax369799.PolynomialQuotient
import Lax369799Proofs.PolynomialContexts

set_option backward.isDefEq.respectTransparency false
namespace Lax369799Proofs.PolynomialQuotient
open Lax369799.RankedSystems Lax369799.Algebras Lax369799.Morphisms Lax369799.Flattening
open Lax369799.PolynomialQuotient Lax369799.PolynomialContexts

private def setoid {B : RankedSet} (E : Algebra B) (F : Set (B 0)) (n : ℕ) : Setoid (B n) where
  r := Equivalent E F
  iseqv := ⟨fun _ _ _ => Iff.rfl, fun h p hp => (h p hp).symm,
    fun h h' p hp => (h p hp).trans (h' p hp)⟩

private noncomputable def representative {B : RankedSet} (E : Algebra B) (F : Set (B 0)) :
    RankedMap (Carrier E F) B := fun _ a => a.out

private noncomputable def evaluate {B : RankedSet} (E : Algebra B) (F : Set (B 0))
    (n : ℕ) (S : System (Carrier E F) n) : Carrier E F n :=
  classMap E F n (E.eval n (relabelSystem (representative E F) S))

private theorem evaluate_representatives {B : RankedSet} (E : Algebra B) (F : Set (B 0))
    (n : ℕ) (S : System B n) :
    evaluate E F n (relabelSystem (classMap E F) S) = classMap E F n (E.eval n S) := by
  apply Quot.sound
  apply PolynomialContexts.evaluation_congruence E F S
    (fun v => representative E F _ (classMap E F _ (S.val.graph.label v).2))
    (fun v => (S.val.graph.label v).2)
  intro v
  exact @Quotient.exact _ (setoid E F _) _ _ (Quot.out_eq (classMap E F _ (S.val.graph.label v).2))

private def relabelMorphism {A B : RankedSet} (η : RankedMap A B) {n : ℕ}
    {S T : SetSystem A n} (f : Morphism S T) : Morphism (relabel η S) (relabel η T) where
  toFun := f.toFun
  initial := f.initial
  root := f.root
  label := fun v => congrArg (fun a : Symbol A => (⟨a.1, η a.1 a.2⟩ : Symbol B)) (f.label v)
  edge := f.edge

/--
---
conclusion: Lax369799.PolynomialQuotient.algebra
---
Choose representatives of the labels, evaluate, and take the resulting
class. Polynomial congruence makes this independent of representatives.
The original algebra laws then descend to the quotient.
-/
theorem algebra {B : RankedSet} (E : Algebra B) (F : Set (B 0)) :
    ∃ Q : Algebra (Carrier E F), ∀ n (S : System B n),
      Q.eval n (relabelSystem (classMap E F) S) = classMap E F n (E.eval n S) := by
  refine ⟨{ eval := evaluate E F, isomorphic := ?_, unit := ?_, associative := ?_ },
    evaluate_representatives E F⟩
  · rintro n S T ⟨f, hf, hc⟩
    exact congrArg (classMap E F n) (E.isomorphic n _ _
      ⟨relabelMorphism (representative E F) f, hf, hc⟩)
  · intro n a
    change classMap E F n (E.eval n (atomicSystem (representative E F n a))) = a
    rw [E.unit]
    exact Quot.out_eq a
  · intro n S T ht
    let U := relabelSystem (fun k R => relabelSystem (representative E F) R) S
    have hu : SystemFlattening U (relabelSystem (representative E F) T) := by
      change relabel (representative E F) T.val = _
      rw [ht]
      rfl
    have he := E.associative n U (relabelSystem (representative E F) T) hu
    have hr := evaluate_representatives E F n
      (relabelSystem (fun k R => E.eval k (relabelSystem (representative E F) R)) S)
    exact hr.trans (congrArg (classMap E F n) he)

/--
---
conclusion: Lax369799.PolynomialQuotient.finite_carrier
---
Every quotient sort is the image of its finite original sort.
-/
theorem finite_carrier {B : RankedSet} (E : Algebra B) (F : Set (B 0))
    (hB : RankwiseFinite B) : RankwiseFinite (Carrier E F) := by
  intro n
  let : Finite (B n) := hB n
  exact Finite.of_surjective (classMap E F n) (fun a => Quot.inductionOn a (fun b => ⟨b, rfl⟩))

/--
---
conclusion: Lax369799.PolynomialQuotient.accepting_class
---
The identity polynomial tests membership in the accepting set itself, so
membership is constant on the closed quotient classes.
-/
theorem accepting_class {B : RankedSet} (E : Algebra B) (F : Set (B 0)) (b : B 0) :
    Accepting E F (classMap E F 0 b) ↔ b ∈ F := by
  constructor
  · rintro ⟨a, ha, hf⟩
    have he := @Quotient.exact _ (setoid E F 0) _ _ ha
    exact (he id Polynomial.variable).mp hf
  · intro h
    exact ⟨b, rfl, h⟩

/--
---
conclusion: Lax369799.PolynomialQuotient.recognition
---
The quotient map commutes with evaluation and preserves the accepting test.
-/
theorem recognition {A B : RankedSet} (E : Algebra B) (F : Set (B 0))
    (Q : Algebra (Carrier E F))
    (hQ : ∀ n (S : System B n), Q.eval n (relabelSystem (classMap E F) S) = classMap E F n (E.eval n S))
    (η : RankedMap A B) (L : Language A) (hL : Recognizes E η F L) :
    Recognizes Q (fun n a => classMap E F n (η n a)) (Accepting E F) L := by
  intro S
  change S ∈ L ↔ Accepting E F (Q.eval 0 (relabelSystem (classMap E F) (relabelSystem η S)))
  rw [hQ, accepting_class]
  exact hL S

end Lax369799Proofs.PolynomialQuotient
