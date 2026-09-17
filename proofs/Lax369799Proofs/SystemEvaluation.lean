import Lax369799.SystemEvaluation
import Lax369799Proofs.Flattening
import Lax369799Proofs.UnfoldEquivalence

namespace Lax369799Proofs.SystemEvaluation
open Lax369799.RankedSystems Lax369799.Morphisms Lax369799.Flattening
open Lax369799.Algebras Lax369799.Renaming Lax369799.Resolutions
open Lax369799Proofs.Pullbacks

private noncomputable def renamedOuter {A : RankedSet} {m n : ℕ}
    (σ : Fin m → Fin n) (S : System A m) : SetSystem (SetSystem A) n :=
  relabel (fun _ (U : System A _) => U.val) (renameSystem σ (atomicSystem S)).val

private noncomputable def renameFlattenMap {A : RankedSet} {m n : ℕ}
    (σ : Fin m → Fin n) (S : System A m) :
    Map (Flattening.graph (renamedOuter σ S)) (rename σ S.val).graph where
  toFun := fun v => by exact v.2
  label := fun _ => rfl
  initial := by intro v h; exact h.2
  root := by
    intro v h
    rcases h with h | ⟨h, _⟩
    · exact h
    · exact False.elim h
  edge := by
    intro v d t ht
    rcases ht with ⟨w, hw, rfl⟩ | ⟨i, hi, ht⟩
    · exact ⟨.inl (by exact w), by exact hw, rfl⟩
    · rcases ht with ⟨w, hw, _, rfl⟩ | ⟨j, hj, rfl⟩
      · obtain ⟨u, ⟨a, he, rfl⟩, hu⟩ := hw
        cases hu
      · obtain ⟨u, ⟨a, he, rfl⟩, hu⟩ := hj
        have ha : (i : Fin m) = a := Fin.ext he
        subst a
        exact ⟨.inr (by exact i), by exact hi, by exact congrArg Sum.inr (Sum.inr.inj hu)⟩

/--
---
conclusion: Lax369799.SystemEvaluation.rename_evaluation
---
Flatten the renamed atomic outer system. Its flattening maps to the
renamed inner system, and a morphism between deterministic systems is a
local cover. Unfold invariance and associativity give the equality.
-/
theorem rename_evaluation {A : RankedSet} (E : Algebra A) (hE : UnfoldInvariant E)
    {m n : ℕ} (σ : Fin m → Fin n) (S : System A m) :
    E.eval n (renameSystem σ S) =
      E.eval n (renameSystem σ (atomicSystem (E.eval m S))) := by
  obtain ⟨U, hU⟩ := Flattening.flatten_system (renameSystem σ (atomicSystem S))
  have f : Morphism U.val (renameSystem σ S).val := by
    change U.val = flatten (renamedOuter σ S) at hU
    rw [hU]
    exact project (renameFlattenMap σ S)
  have he := hE n (renameSystem σ S) U
    ⟨U.val, ⟨f, MorphismTheorems.system_morphism_locally_surjective U (renameSystem σ S) f⟩,
      ⟨MorphismTheorems.identity U.val, MorphismTheorems.identity_surjective U.val⟩⟩
  have ha := E.associative n (renameSystem σ (atomicSystem S)) U hU
  exact he.trans ha.symm

/--
---
conclusion: Lax369799.SystemEvaluation.rename_congruence
---
Evaluate the two systems before applying the common variable renaming.
-/
theorem rename_congruence {A : RankedSet} (E : Algebra A) (hE : UnfoldInvariant E)
    {m n : ℕ} (σ : Fin m → Fin n) (S T : System A m) (h : E.eval m S = E.eval m T) :
    E.eval n (renameSystem σ S) = E.eval n (renameSystem σ T) := by
  rw [rename_evaluation E hE σ S, rename_evaluation E hE σ T, h]

/--
---
conclusion: Lax369799.SystemEvaluation.context_evaluation
---
The context labelled by atomic ordinary letters and the supplied hole
system is deterministic. Associativity evaluates its flattening by first
evaluating its labels; the unit law restores the ordinary letters.
-/
theorem context_evaluation {A : RankedSet} (E : Algebra A) {k n : ℕ}
    (C : SetContext A k n) (hC : C.system.Deterministic) (S : System A k) :
    ∃ U : System A n, U.val = plug C S.val ∧
      E.eval n U = E.eval n (relabelSystem (Lax369799.SystemEvaluation.fillLetter (E.eval k S))
        ⟨C.system, hC⟩) := by
  let T := relabelSystem (Lax369799.SystemEvaluation.substituteSystem S) ⟨C.system, hC⟩
  obtain ⟨U, hU⟩ := Flattening.flatten_system T
  have hval : (fun r a => (Lax369799.SystemEvaluation.substituteSystem S r a).val) =
      substitution S.val := by
    funext r a
    cases a with
    | inl a => rfl
    | inr h => obtain ⟨h⟩ := h; subst r; rfl
  have heval : (fun r a => E.eval r (Lax369799.SystemEvaluation.substituteSystem S r a)) =
      Lax369799.SystemEvaluation.fillLetter (E.eval k S) := by
    funext r a
    cases a with
    | inl a => exact E.unit r a
    | inr h => obtain ⟨h⟩ := h; subst r; rfl
  refine ⟨U, ?_, ?_⟩
  · change U.val = flatten (relabel (substitution S.val) C.system)
    change U.val = flatten (relabel (fun r a =>
      (Lax369799.SystemEvaluation.substituteSystem S r a).val) C.system) at hU
    rw [hval] at hU
    exact hU
  · have hh := (E.associative n T U hU).symm
    have he : relabelSystem E.eval T =
        relabelSystem (Lax369799.SystemEvaluation.fillLetter (E.eval k S)) ⟨C.system, hC⟩ := by
      apply Subtype.ext
      change relabel (fun r a => E.eval r (Lax369799.SystemEvaluation.substituteSystem S r a)) C.system = _
      rw [heval]
      rfl
    exact hh.trans (congrArg (E.eval n) he)

end Lax369799Proofs.SystemEvaluation
