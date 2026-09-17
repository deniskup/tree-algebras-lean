import Lax369799.Algebras
import Lax369799.MonadicSecondOrder
import Lax369799.TransitionEncoding

/-!
---
title: MSO-definable languages are algebraically recognisable
type: theorem
---
An MSO sentence on finite transition systems defines, through decoding, a
language of ranked systems recognised by a rankwise-finite algebra.
This is `lemma:MSO-is-recognisable` in Section 6.2. The vocabulary uses a
finite set of proposition letters uniformly across all ranks.
-/

namespace Lax369799.MSORecognition
open Algebras TransitionEncoding

axiom mso_recognizable {P : Type} [Finite P] (φ : MonadicSecondOrder.Sentence P) :
  Recognizable {S | MonadicSecondOrder.Models (decode S) φ}

end Lax369799.MSORecognition
