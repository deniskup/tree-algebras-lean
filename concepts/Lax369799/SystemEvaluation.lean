import Lax369799.Renaming

/-!
---
title: Evaluation and variable renaming in regular-tree algebras
type: theorem
---
Renaming the variables of a system depends only on its algebra value.
This follows by flattening a renamed atomic outer system and applies
also to noninjective variable maps.
-/
namespace Lax369799.SystemEvaluation
open RankedSystems Algebras Renaming

axiom rename_evaluation {A : RankedSet} (E : Algebra A) (hE : UnfoldInvariant E)
    {m n : ℕ} (σ : Fin m → Fin n) (S : System A m) :
    E.eval n (renameSystem σ S) =
      E.eval n (renameSystem σ (atomicSystem (E.eval m S)))

axiom rename_congruence {A : RankedSet} (E : Algebra A) (hE : UnfoldInvariant E)
    {m n : ℕ} (σ : Fin m → Fin n) (S T : System A m) (h : E.eval m S = E.eval m T) :
    E.eval n (renameSystem σ S) = E.eval n (renameSystem σ T)

end Lax369799.SystemEvaluation
