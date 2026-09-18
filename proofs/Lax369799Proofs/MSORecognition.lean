import Lax369799.MSORecognition
import Lax369799Proofs.SetLogicRecognition
import Lax369799Proofs.SetLogicTranslation

set_option backward.isDefEq.respectTransparency false
namespace Lax369799Proofs.MSORecognition
open Lax369799.Algebras Lax369799.RankedSystems Lax369799.TransitionEncoding
open Lax369799.SetLogicRecognition Lax369799.SetLogicTranslation

/--
---
conclusion: Lax369799.MSORecognition.mso_recognizable
---
Translate vertex variables into singleton-valued set variables. Finite
path algebras recognize the atomic formulas; products, complement, and
nonempty powerset algebras implement the logical operations. A sentence
has no free marks, which are removed by inverse relabelling.
-/
theorem mso_recognizable {P : Type} [Finite P] (φ : Lax369799.MonadicSecondOrder.Sentence P) :
    Recognizable {S | Lax369799.MonadicSecondOrder.Models (decode S) φ} := by
  let ψ := translate φ (X := Empty) Fin.elim0 Fin.elim0
  have hψ := SetLogicRecognition.recognizable (SetLogicRecognition.atomic_recognizable P) ψ
  have h := RecognitionClosure.inverse_relabel (A := TransitionAlphabet P)
    (fun _ a => (a, (∅ : Set Empty))) (language ψ) hψ
  convert h using 1
  ext S
  exact (SetLogicTranslation.correct (decode S) φ (X := Empty) Fin.elim0 Fin.elim0
    (fun _ => ∅) Fin.elim0 Fin.elim0 (fun i => Fin.elim0 i) (fun i => Fin.elim0 i)).symm

end Lax369799Proofs.MSORecognition
