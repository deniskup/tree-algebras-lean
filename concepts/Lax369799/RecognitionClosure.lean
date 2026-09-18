import Lax369799.Algebras

/-!
---
title: Boolean closure and inverse relabelling of recognizable languages
type: theorem
---
Rankwise-finite algebraic recognition is preserved by Boolean operations
and inverse relabelling. Products combine recognizing algebras; complement
changes the accepting subset, and inverse relabelling composes letter maps.
These are the Boolean and cylindrification clauses of Section 3.
-/
namespace Lax369799.RecognitionClosure
open RankedSystems Algebras

axiom complement {A : RankedSet} (L : Language A) (h : Recognizable L) : Recognizable Lᶜ

axiom intersection {A : RankedSet} (L K : Language A)
    (hL : Recognizable L) (hK : Recognizable K) : Recognizable (L ∩ K)

axiom union {A : RankedSet} (L K : Language A)
    (hL : Recognizable L) (hK : Recognizable K) : Recognizable (L ∪ K)

axiom inverse_relabel {A B : RankedSet} (η : RankedMap A B) (L : Language B)
    (hL : Recognizable L) : Recognizable {S | relabelSystem η S ∈ L}

end Lax369799.RecognitionClosure
