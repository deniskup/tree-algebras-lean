import Lax369799.QuantitativeRecognition
import Lax369799Proofs.MSORecognition
import Lax369799Proofs.RecognitionClosure
import Lax369799Proofs.RecognitionProjection
import Mathlib.Tactic.Ring
import Mathlib.Data.Finite.Sum
import Mathlib.SetTheory.Cardinal.NatCard

set_option backward.isDefEq.respectTransparency false
namespace Lax369799Proofs.QuantitativeRecognition
open Lax369799
open RankedSystems Algebras SetLogic SetLogicRecognition TransitionEncoding
open Lax369799.QuantitativeRecognition

private theorem mono {A : RankedSet} (L : Language A) {f g : ℕ → ℕ}
    (h : Bound f L) (hg : ∀ k,f k ≤ g k) : Bound g L := by
  obtain ⟨B,E,η,F,hB,hr,hb⟩ := h
  exact ⟨B,E,η,F,hB,hr,fun k => (hb k).trans (hg k)⟩

private theorem complement {A : RankedSet} (L : Language A) {f : ℕ → ℕ}
    (h : Bound f L) : Bound f Lᶜ := by
  obtain ⟨B,E,η,F,hB,hr,hb⟩ := h
  exact ⟨B,E,η,Fᶜ,hB,fun S => not_congr (hr S),hb⟩

private theorem union {A : RankedSet} (L K : Language A) {f g : ℕ → ℕ}
    (hL : Bound f L) (hK : Bound g K) : Bound (fun k => f k*g k) (L ∪ K) := by
  obtain ⟨B,E,η,F,hB,hL,hb⟩ := hL
  obtain ⟨C,G,μ,H,hC,hK,hc⟩ := hK
  refine ⟨(fun n => B n × C n),RecognitionClosure.product E G,
    (fun n a => (η n a,μ n a)),{b | b.1 ∈ F ∨ b.2 ∈ H},
    RecognitionClosure.product_finite hB hC,fun S => or_congr (hL S) (hK S),?_⟩
  intro k
  rw [Nat.card_prod]
  exact Nat.mul_le_mul (hb k) (hc k)

private theorem inverse_relabel {A B : RankedSet} (η : RankedMap A B) (L : Language B)
    {f : ℕ → ℕ} (h : Bound f L) : Bound f {S | relabelSystem η S ∈ L} := by
  obtain ⟨C,E,μ,F,hC,hr,hb⟩ := h
  exact ⟨C,E,(fun n a => μ n (η n a)),F,hC,fun S => hr (relabelSystem η S),hb⟩

private theorem projection {A B : RankedSet} (η : RankedMap A B)
    (hη : ∀ n,Function.Surjective (η n)) (L : Language A) {f : ℕ → ℕ}
    (hL : Bound f L) : Bound (fun k => 2 ^ f k) (RecognitionProjection.Projected η L) := by
  classical
  obtain ⟨C,E,μ,F,hC,hL,hb⟩ := hL
  obtain ⟨E',he⟩ := NonemptyPowersets.algebra E
  let ν : RankedMap B (NonemptyPowersets.Carrier C) := fun n b =>
    ⟨{c | ∃ a,η n a = b ∧ μ n a = c},by
      obtain ⟨a,ha⟩ := hη n b
      exact ⟨μ n a,a,ha,rfl⟩⟩
  refine ⟨NonemptyPowersets.Carrier C,E',ν,{X | ∃ c ∈ X.val,c ∈ F},
    NonemptyPowersets.finite_carrier hC,?_,?_⟩
  · intro S
    change (∃ q,(∀ v,η _ (q v) = (S.val.graph.label v).2) ∧ PolynomialContexts.withLabels S q ∈ L) ↔ _
    change _ ↔ ∃ c ∈ (E'.eval 0 (relabelSystem ν S)).val,c ∈ F
    rw [he]
    constructor
    · rintro ⟨q,hq,hl⟩
      exact ⟨E.eval 0 (relabelSystem μ (PolynomialContexts.withLabels S q)),
        ⟨fun v => μ _ (q v),fun v => ⟨q v,hq v,rfl⟩,rfl⟩,(hL _).mp hl⟩
    · rintro ⟨c,⟨q,hq,hv⟩,hc⟩
      change ∀ v,∃ a,η _ a = (S.val.graph.label v).2 ∧ μ _ a = q v at hq
      choose p hp hμ using hq
      refine ⟨p,hp,(hL _).mpr ?_⟩
      have ht : relabelSystem μ (PolynomialContexts.withLabels S p) =
          PolynomialContexts.withLabels (relabelSystem ν S) q := by
        change PolynomialContexts.withLabels S (fun v => μ _ (p v)) = _
        simp only [hμ]; rfl
      rw [ht,hv]; exact hc
  · intro k
    let : Finite (C k) := hC k
    let : Fintype (C k) := Fintype.ofFinite (C k)
    have hc := Nat.card_le_card_of_injective (fun s : NonemptyPowersets.Carrier C k => s.val)
      Subtype.val_injective
    have hset : Nat.card (Set (C k)) = 2 ^ Nat.card (C k) := by
      simp [Nat.card_eq_fintype_card]
    exact hc.trans (hset.le.trans (Nat.pow_le_pow_right (by decide) (hb k)))

private theorem path_card (Q : Type) [Fintype Q] (k : ℕ) :
    Nat.card (PathAlgebra.Carrier Q k) = 2 ^ (Fintype.card Q*(Fintype.card Q*(k+1))) := by
  classical
  simp only [PathAlgebra.Carrier,PathAlgebra.Result,Nat.card_eq_fintype_card,
    Fintype.card_fun,Fintype.card_set,Fintype.card_sum,Fintype.card_prod,Fintype.card_fin]
  rw [← Nat.pow_mul]
  congr 1
  ring

private theorem occurrence {A : RankedSet} (p : ∀ n,A n → Prop) :
    Bound (fun k => 2 ^ (k+1)) {S : System A 0 | ∃ v,p _ (S.val.graph.label v).2} := by
  obtain ⟨E,he⟩ := PathAlgebra.algebra Unit
  refine ⟨PathAlgebra.Carrier Unit,E,LocalRecognition.occurrenceLetter p,
    {a | .inl () ∈ a ()},PathAlgebra.finite_carrier Unit,?_,?_⟩
  · intro S
    rw [he]
    exact (LocalRecognition.occurrence_iff p S).symm
  · intro k
    simp only [path_card,Fintype.card_unit,Nat.one_mul,le_refl]

private theorem edge {A : RankedSet} (p q : ∀ n,A n → Prop) :
    Bound (fun k => 2 ^ (4*(k+1))) {S : System A 0 | ∃ v w d,
      p _ (S.val.graph.label v).2 ∧ q _ (S.val.graph.label w).2 ∧ S.val.graph.edge v d (.inl w)} := by
  obtain ⟨E,he⟩ := PathAlgebra.algebra Bool
  refine ⟨PathAlgebra.Carrier Bool,E,LocalRecognition.edgeLetter p q,
    {a | .inl true ∈ a false},PathAlgebra.finite_carrier Bool,?_,?_⟩
  · intro S
    rw [he]
    exact (LocalRecognition.edge_iff p q S).symm
  · intro k
    simp only [path_card,Fintype.card_bool]
    exact le_of_eq (congrArg (2 ^ ·) (by omega))

private theorem initial {P X : Type} (x : X) :
    Bound (fun k => 2 ^ (4*(k+1))) (language (Formula.initial (P := P) x)) := by
  classical
  obtain ⟨E,he⟩ := InitialAlgebra.algebra Bool
  refine ⟨(fun _ => Bool),E,(fun _ a => decide (x ∈ a.2)),{true},fun _ => inferInstance,?_,?_⟩
  · intro S
    rw [he]
    exact (decide_eq_true_iff).symm
  · intro k
    have h : 2 ≤ 2 ^ (4*(k+1)) := Nat.le_pow (by omega)
    simpa [Nat.card_eq_fintype_card] using h

private theorem recognizable {P X : Type} [hX : Finite X] (φ : Formula P X) :
    Bound (logicBound φ) (language φ) := by
  classical
  revert hX
  induction φ with
  | subset x y =>
    intro hX
    have h := complement _ (occurrence (A := Alphabet P _) (fun _ a => x ∈ a.2 ∧ y ∉ a.2))
    have he : language (Formula.subset (P := P) x y) =
        {S : System (Alphabet P _) 0 | ∃ v,x ∈ (S.val.graph.label v).2.2 ∧ y ∉ (S.val.graph.label v).2.2}ᶜ := by
      ext S
      simp only [language,Formula.eval,Set.mem_ofPred_eq,Set.mem_compl_iff,Set.subset_def,
        not_exists,not_and,not_not]
      rfl
    rw [he]
    exact mono _ h (fun k => Nat.pow_le_pow_right (by decide) (by omega))
  | initial x => intro hX; exact initial x
  | proposition p x =>
    intro hX
    have h := complement _ (occurrence (A := Alphabet P _) (fun _ a => x ∈ a.2 ∧ p ∉ a.1))
    have he : language (Formula.proposition p x) =
        {S : System (Alphabet P _) 0 | ∃ v,x ∈ (S.val.graph.label v).2.2 ∧ p ∉ (S.val.graph.label v).2.1}ᶜ := by
      ext S
      simp only [language,Formula.eval,Set.mem_ofPred_eq,Set.mem_compl_iff,not_exists,not_and,not_not]
      rfl
    rw [he]
    exact mono _ h (fun k => Nat.pow_le_pow_right (by decide) (by omega))
  | edge x y =>
    intro hX
    have h := edge (A := Alphabet P _) (fun _ a => x ∈ a.2) (fun _ a => y ∈ a.2)
    change Bound (logicBound (Formula.edge (P := P) x y)) _ at h
    convert h using 1
    ext S
    change (∃ v,x ∈ (S.val.graph.label v).2.2 ∧ ∃ w,y ∈ (S.val.graph.label w).2.2 ∧
      ∃ d,S.val.graph.edge v d (.inl w)) ↔ _
    constructor
    · rintro ⟨v,hx,w,hy,d,hd⟩; exact ⟨v,w,d,hx,hy,hd⟩
    · rintro ⟨v,w,d,hx,hy,hd⟩; exact ⟨v,hx,w,hy,d,hd⟩
  | neg φ ih => intro hX; exact complement _ ih
  | disj φ ψ ihφ ihψ => intro hX; exact union _ _ ihφ ihψ
  | existsSet φ ih =>
    intro hX
    rw [SetLogicRecognition.projection_language]
    exact projection SetLogicRecognition.forget (fun _ a => ⟨(a.1,fun x => x.elim False a.2),rfl⟩) _ ih

/--
---
conclusion: Lax369799.QuantitativeRecognition.mso_bound
---
Track the finite carrier sizes in the recognition induction. Atomic path
summaries have at most 2^(4(k+1)) values in sort k. Disjunction multiplies
bounds, existential quantification takes a powerset, and inverse relabelling
preserves the bound. The bound is computed directly from the input syntax.
-/
theorem mso_bound {P : Type} [Finite P] (φ : MonadicSecondOrder.Sentence P) :
    Bound (msoBound φ) {S | MonadicSecondOrder.Models (decode S) φ} := by
  let ψ := SetLogicTranslation.translate φ (X := Empty) Fin.elim0 Fin.elim0
  have hψ := recognizable ψ
  have h := inverse_relabel (A := TransitionAlphabet P) (fun _ a => (a,(∅ : Set Empty))) (language ψ) hψ
  change Bound (msoBound φ) {S | RankedSystems.relabelSystem (fun _ a => (a,(∅ : Set Empty))) S ∈ language ψ} at h
  convert h using 1
  ext S
  exact (SetLogicTranslation.correct (decode S) φ (X := Empty) Fin.elim0 Fin.elim0
    (fun _ => ∅) Fin.elim0 Fin.elim0 (fun i => Fin.elim0 i) (fun i => Fin.elim0 i)).symm

end Lax369799Proofs.QuantitativeRecognition
