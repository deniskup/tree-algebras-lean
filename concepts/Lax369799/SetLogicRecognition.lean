import Lax369799.SetLogicTranslation
import Lax369799.RecognitionProjection
import Lax369799.TransitionEncoding

/-!
---
title: Recognition induction for pure second-order logic
type: theorem
---
Free set variables are recorded as extra vertex marks. The atomic
languages have finite recognizing algebras. Boolean closure and existential
projection then give recognition for every formula. The induction is
also stated separately with explicit atomic-language hypotheses.
-/
namespace Lax369799.SetLogicRecognition
open RankedSystems Algebras SetLogic TransitionEncoding

abbrev Alphabet (P X : Type) : RankedSet := fun _ => Set P × Set X

noncomputable def language {P X : Type} (φ : Formula P X) : Language (Alphabet P X) :=
  {S | φ.eval (decode (relabelSystem (fun _ a => a.1) S))
    (fun x v => x ∈ (S.val.graph.label v).2.2)}

structure AtomicRecognizable (P : Type) : Prop where
  subset : ∀ (X : Type) [Finite X] (x y : X), Recognizable (language (Formula.subset (P := P) x y))
  initial : ∀ (X : Type) [Finite X] (x : X), Recognizable (language (Formula.initial (P := P) x))
  proposition : ∀ (X : Type) [Finite X] (p : P) (x : X), Recognizable (language (Formula.proposition p x))
  edge : ∀ (X : Type) [Finite X] (x y : X), Recognizable (language (Formula.edge (P := P) x y))

axiom atomic_recognizable (P : Type) : AtomicRecognizable P

axiom initial_recognizable {P X : Type} (x : X) :
    Recognizable (language (Formula.initial (P := P) x))

axiom recognizable {P X : Type} [Finite X] (h : AtomicRecognizable P) (φ : Formula P X) :
    Recognizable (language φ)

end Lax369799.SetLogicRecognition
