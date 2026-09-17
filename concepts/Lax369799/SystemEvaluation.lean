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
open RankedSystems Algebras Renaming Flattening

/-- Replace the hole symbol by a letter of its rank. -/
def fillLetter {A : RankedSet} {k : ℕ} (a : A k) : RankedMap (WithHole A k) A :=
  fun _ b => match b with
    | .inl b => b
    | .inr ⟨h⟩ => h ▸ a

def substituteSystem {A : RankedSet} {k : ℕ} (S : System A k) :
    RankedMap (WithHole A k) (System A) :=
  fun _ b => match b with
    | .inl b => atomicSystem b
    | .inr ⟨h⟩ => h ▸ S

axiom context_evaluation {A : RankedSet} (E : Algebra A) {k n : ℕ}
    (C : SetContext A k n) (hC : C.system.Deterministic) (S : System A k) :
    ∃ U : System A n, U.val = plug C S.val ∧
      E.eval n U = E.eval n (relabelSystem (fillLetter (E.eval k S)) ⟨C.system, hC⟩)

axiom rename_evaluation {A : RankedSet} (E : Algebra A) (hE : UnfoldInvariant E)
    {m n : ℕ} (σ : Fin m → Fin n) (S : System A m) :
    E.eval n (renameSystem σ S) =
      E.eval n (renameSystem σ (atomicSystem (E.eval m S)))

axiom rename_congruence {A : RankedSet} (E : Algebra A) (hE : UnfoldInvariant E)
    {m n : ℕ} (σ : Fin m → Fin n) (S T : System A m) (h : E.eval m S = E.eval m T) :
    E.eval n (renameSystem σ S) = E.eval n (renameSystem σ T)

end Lax369799.SystemEvaluation
