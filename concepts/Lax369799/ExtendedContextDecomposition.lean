import Lax369799.ExtendedContexts
import Lax369799.SetSystemAlgebras

/-!
---
title: Evaluation of closed contexts through extended unary pieces
type: theorem
---
The unary pieces of a closed context, together with their immediate
initial/root markers, determine its evaluation for every hole label.
This is the algebraic form of context decomposition (Lemmas 44 and 66).
Initial and root marks remain distinct, and every vertex of each piece
is retained. It applies to arbitrary set-algebras without an assumption
that planting preserves acceptance.
-/

namespace Lax369799.ExtendedContextDecomposition
open RankedSystems (RankedSet)
open FinitePresentations FiniteContexts

axiom context_decomposition {A : RankedSet} (E : SetSystemAlgebras.SetAlgebra A)
    {k : ℕ} (C : Context A k 0) :
    ∃ p : ExtendedContexts.Pieces A k, ∀ a : A k,
      E.eval 0 (plug (ExtendedContexts.context p) (atomic a)) = E.eval 0 (plug C (atomic a))

end Lax369799.ExtendedContextDecomposition
