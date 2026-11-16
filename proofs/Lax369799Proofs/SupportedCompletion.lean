import Lax369799.SupportedCompletion
import Lax369799Proofs.SystemMonad

namespace Lax369799Proofs.SupportedCompletion
set_option backward.isDefEq.respectTransparency false
open Lax369799
open RankedSystems Morphisms
open SupportEvaluation (Carrier classMap Equivalent profile)

private def relationSetoid {B : RankedSet} (E : SupportedAlgebras.Algebra B) (n : ℕ) :
    Setoid (System B n) where
  r := Equivalent E
  iseqv := ⟨fun _ => rfl,Eq.symm,Eq.trans⟩

private noncomputable def representative {B : RankedSet} (E : SupportedAlgebras.Algebra B) :
    RankedMap (Carrier E) (System B) := fun _ a => a.out

private noncomputable def flatten {B : RankedSet} {n : ℕ} (P : System (System B) n) :
    System B n := Classical.choose (Flattening.flatten_system P)

private theorem flatten_spec {B : RankedSet} {n : ℕ} (P : System (System B) n) :
    Lax369799.Flattening.SystemFlattening P (flatten P) :=
  Classical.choose_spec (Flattening.flatten_system P)

private noncomputable def evaluate {B : RankedSet} (E : SupportedAlgebras.Algebra B)
    (n : ℕ) (P : System (Carrier E) n) : Carrier E n :=
  classMap E n (flatten (relabelSystem (representative E) P))

private theorem evaluate_representatives {B : RankedSet} (E : SupportedAlgebras.Algebra B)
    (n : ℕ) (P : System (System B) n) (U : System B n)
    (hU : Lax369799.Flattening.SystemFlattening P U) :
    evaluate E n (relabelSystem (classMap E) P) = classMap E n U := by
  apply Quot.sound
  apply SubstitutionProfiles.pointwise_congruence E P
    (fun v => representative E _ (classMap E _ (P.val.graph.label v).2))
    (fun v => (P.val.graph.label v).2) ?_
    (flatten (relabelSystem (representative E) (relabelSystem (classMap E) P))) U
    (flatten_spec _) hU
  intro v
  exact @Quotient.exact _ (relationSetoid E _) _ _
    (Quot.out_eq (classMap E _ (P.val.graph.label v).2))

/--
---
conclusion: Lax369799.SupportedCompletion.algebra
---
-/
theorem algebra {B : RankedSet} (E : SupportedAlgebras.Algebra B) :
    ∃ D : Algebras.Algebra (Carrier E), ∀ n (P : System (System B) n) (U : System B n),
      Lax369799.Flattening.SystemFlattening P U →
        D.eval n (relabelSystem (classMap E) P) = classMap E n U := by
  classical
  refine ⟨{eval := evaluate E,isomorphic := ?_,unit := ?_,associative := ?_},evaluate_representatives E⟩
  · rintro n S T ⟨f,hf,hc⟩
    apply Quot.sound
    apply SupportIsomorphism.profile_isomorphic E
    exact SystemMonad.flatten_isomorphic
      (relabelSystem (representative E) S) (relabelSystem (representative E) T) _ _
      (flatten_spec _) (flatten_spec _)
      ⟨SystemSubstitution.relabelMorphism (representative E) f,hf,hc⟩
  · intro n a
    change classMap E n (flatten (atomicSystem (representative E n a))) = a
    have hi := SystemMonad.outer_unit (representative E n a) _ (flatten_spec _)
    exact (Quot.sound (SupportIsomorphism.profile_isomorphic E _ _ hi)).trans (Quot.out_eq a)
  · intro n S T hT
    let P : System (System (System B)) n :=
      relabelSystem (fun k R => relabelSystem (representative E) R) S
    let Q := relabelSystem (representative E) T
    have hQ : Lax369799.Flattening.SystemFlattening P Q := by
      change relabel (representative E) T.val = _
      rw [hT]
      rfl
    let t := fun v : P.val.Vertex => flatten (P.val.graph.label v).2
    let V := flatten (PolynomialContexts.withLabels P t)
    have hAssoc := SystemMonad.associative P Q (flatten Q) t V hQ (flatten_spec Q)
      (fun _ => flatten_spec _) (flatten_spec _)
    have hLeft : relabelSystem (evaluate E) S =
        relabelSystem (classMap E) (PolynomialContexts.withLabels P t) := rfl
    change evaluate E n (relabelSystem (evaluate E) S) = classMap E n (flatten Q)
    rw [hLeft,evaluate_representatives E n _ V (flatten_spec _)]
    exact Quot.sound (SupportIsomorphism.profile_isomorphic E V (flatten Q)
      (SystemIsomorphisms.iso_symm hAssoc))

/--
---
conclusion: Lax369799.SupportedCompletion.legacy_recognizable
---
-/
theorem legacy_recognizable {A : RankedSet} (L : Algebras.Language A)
    (hL : SupportedAlgebras.Recognizable L) : Algebras.Recognizable L := by
  classical
  obtain ⟨B,E,η,F,hB,hrec⟩ := hL
  obtain ⟨D,hD⟩ := algebra E
  obtain ⟨e,he⟩ := SupportEvaluation.closed_carrier E
  let letter : RankedMap A (Carrier E) := fun n a => classMap E n (atomicSystem (η n a))
  refine ⟨Carrier E,D,letter,{c | e c ∈ F},SupportEvaluation.finite_carrier E hB,?_⟩
  intro S
  let R := relabelSystem η S
  let P := relabelSystem (fun _ b => atomicSystem b) R
  obtain ⟨U,hU⟩ := Flattening.flatten_system P
  have hPres := hD 0 P U hU
  have hIso := SystemMonad.inner_unit R U hU
  have hClass : classMap E 0 U = classMap E 0 R :=
    Quot.sound (SupportIsomorphism.profile_isomorphic E U R hIso)
  have hEval : D.eval 0 (relabelSystem letter S) = classMap E 0 R := hPres.trans hClass
  change S ∈ L ↔ e (D.eval 0 (relabelSystem letter S)) ∈ F
  rw [hEval,he R]
  exact hrec ((SupportedSystems.closedEquiv A).symm S)

/--
---
conclusion: Lax369799.SupportedCompletion.recognizable_iff
---
-/
theorem recognizable_iff {A : RankedSet} (L : Algebras.Language A) :
    SupportedAlgebras.Recognizable L ↔ Algebras.Recognizable L :=
  ⟨legacy_recognizable L,SupportedAlgebras.legacy_recognizable L⟩

end Lax369799Proofs.SupportedCompletion
