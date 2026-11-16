import Lax369799.SetLogicRecognition
import Lax369799Proofs.RecognitionProjection
import Lax369799Proofs.RecognitionClosure
import Lax369799Proofs.InitialAlgebra
import Lax369799Proofs.LocalRecognition

set_option backward.isDefEq.respectTransparency false
namespace Lax369799Proofs.SetLogicRecognition
open Lax369799.RankedSystems Lax369799.Algebras Lax369799.PolynomialContexts
open Lax369799.SetLogic Lax369799.SetLogicRecognition Lax369799.TransitionEncoding
open Lax369799.RecognitionProjection

def forget {P X : Type} : RankedMap (Alphabet P (Option X)) (Alphabet P X) :=
  fun _ a => (a.1, fun x => a.2 (some x))

theorem projection_language {P X : Type} (φ : Formula P (Option X)) :
    language (.existsSet φ) = Projected forget (language φ) := by
  ext S
  change (∃ U, φ.eval (decode (relabelSystem (fun _ a => a.1) S))
    (fun x => x.elim U (fun y v => y ∈ (S.val.graph.label v).2.2))) ↔ _
  constructor
  · rintro ⟨U, hu⟩
    refine ⟨fun v => ((S.val.graph.label v).2.1,
      fun x => x.elim (v ∈ U) (fun y => y ∈ (S.val.graph.label v).2.2)), fun _ => rfl, ?_⟩
    change φ.eval _ _
    convert hu using 1 <;> first | rfl | (funext x v; cases x <;> rfl)
  · rintro ⟨q, hq, hφ⟩
    let U : Set S.val.Vertex := fun v => (q v).2 none
    have he : q = fun v => ((S.val.graph.label v).2.1,
        fun x => x.elim (v ∈ U) (fun y => y ∈ (S.val.graph.label v).2.2)) := by
      funext v
      apply Prod.ext
      · exact congrArg (fun a : Set P × Set X => a.1) (hq v)
      · funext x
        cases x with
        | none => rfl
        | some y => exact congrFun (congrArg Prod.snd (hq v)) y
    rw [he] at hφ
    refine ⟨U, ?_⟩
    change φ.eval _ _ at hφ
    convert hφ using 1 <;> first | rfl | (funext x v; cases x <;> rfl)

/--
---
conclusion: Lax369799.SetLogicRecognition.initial_recognizable
---
The initial-label algebra reads the chosen mark at the initial vertex.
-/
theorem initial_recognizable {P X : Type} (x : X) :
    Recognizable (language (Formula.initial (P := P) x)) :=
  InitialAlgebra.recognizes (A := Alphabet P X) (fun _ a => x ∈ a.2)

/--
---
conclusion: Lax369799.SetLogicRecognition.atomic_recognizable
---
Inclusion and universal proposition predicates exclude a bad vertex.
Existential edge predicates are recognized by the two-state path algebra.
-/
theorem atomic_recognizable (P : Type) : AtomicRecognizable P := by
  classical
  constructor
  · intro X _ x y
    have h := RecognitionClosure.complement _
      (LocalRecognition.occurrence (A := Alphabet P X) (fun _ a => x ∈ a.2 ∧ y ∉ a.2))
    convert h using 1
    ext S
    simp only [language, Formula.eval, Set.mem_ofPred_eq, Set.mem_compl_iff,
      Set.subset_def, not_exists, not_and, not_not]
    rfl
  · intro X _ x
    exact initial_recognizable x
  · intro X _ p x
    have h := RecognitionClosure.complement _
      (LocalRecognition.occurrence (A := Alphabet P X) (fun _ a => x ∈ a.2 ∧ p ∉ a.1))
    convert h using 1
    ext S
    simp only [language, Formula.eval, Set.mem_ofPred_eq, Set.mem_compl_iff,
      not_exists, not_and, not_not]
    rfl
  · intro X _ x y
    have h := LocalRecognition.edge (A := Alphabet P X) (fun _ a => x ∈ a.2) (fun _ a => y ∈ a.2)
    convert h using 1
    ext S
    change (∃ v, x ∈ (S.val.graph.label v).2.2 ∧ ∃ w, y ∈ (S.val.graph.label w).2.2 ∧
      ∃ d, S.val.graph.edge v d (.inl w)) ↔ _
    constructor
    · rintro ⟨v, hx, w, hy, d, hd⟩
      exact ⟨v, w, d, hx, hy, hd⟩
    · rintro ⟨v, w, d, hx, hy, hd⟩
      exact ⟨v, hx, w, hy, d, hd⟩

/--
---
conclusion: Lax369799.SetLogicRecognition.recognizable
---
Boolean operations use product algebras. Quantification forgets the new
mark and uses the nonempty powerset algebra.
-/
theorem recognizable {P X : Type} [hX : Finite X] (h : AtomicRecognizable P) (φ : Formula P X) :
    Recognizable (language φ) := by
  revert hX
  induction φ with
  | subset x y => intro hX; exact h.subset _ x y
  | initial x => intro hX; exact h.initial _ x
  | proposition p x => intro hX; exact h.proposition _ p x
  | edge x y => intro hX; exact h.edge _ x y
  | neg φ ih => intro hX; exact RecognitionClosure.complement _ ih
  | disj φ ψ ihφ ihψ => intro hX; exact RecognitionClosure.union _ _ ihφ ihψ
  | existsSet φ ih =>
    intro hX
    rw [projection_language]
    apply RecognitionProjection.recognizable forget _ _ ih
    intro n a
    exact ⟨(a.1, fun x => x.elim False a.2), rfl⟩

end Lax369799Proofs.SetLogicRecognition
