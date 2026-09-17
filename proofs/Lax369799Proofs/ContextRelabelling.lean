import Lax369799.ContextRelabelling
import Lax369799Proofs.SystemEvaluation

namespace Lax369799Proofs.ContextRelabelling
open Lax369799.RankedSystems Lax369799.Flattening Lax369799.ContextRelabelling

/--
---
conclusion: Lax369799.ContextRelabelling.relabel_plug
---
Relabelling commutes with flattening. For an ordinary letter the two
substitutions are atomic, and at the hole both use the relabelled argument.
-/
theorem relabel_plug {A B : RankedSet} (η : RankedMap A B) {k n : ℕ}
    (C : SetContext A k n) (S : SetSystem A k) :
    relabel η (plug C S) = plug (mapContext η C) (relabel η S) := by
  have h : (fun r a => relabel η (substitution S r a)) =
      (fun r a => substitution (relabel η S) r (mapAlphabet η k r a)) := by
    funext r a
    cases a with
    | inl a => rfl
    | inr hr => obtain ⟨hr⟩ := hr; subst r; rfl
  change flatten (relabel (fun r a => relabel η (substitution S r a)) C.system) = _
  rw [h]
  rfl

/--
---
conclusion: Lax369799.ContextRelabelling.plug_system
---
Replace the ordinary letters by atomic systems and the hole by its
argument. This deterministic outer system has a deterministic flattening.
-/
theorem plug_system {A : RankedSet} {k n : ℕ}
    (C : SetContext A k n) (hC : C.system.Deterministic) (S : System A k) :
    ∃ U : System A n, U.val = plug C S.val := by
  let T := relabelSystem (Lax369799.SystemEvaluation.substituteSystem S) ⟨C.system, hC⟩
  obtain ⟨U, hU⟩ := Flattening.flatten_system T
  have hval : (fun r a => (Lax369799.SystemEvaluation.substituteSystem S r a).val) =
      substitution S.val := by
    funext r a
    cases a with
    | inl a => rfl
    | inr h => obtain ⟨h⟩ := h; subst r; rfl
  refine ⟨U, ?_⟩
  change U.val = flatten (relabel (fun r a =>
    (Lax369799.SystemEvaluation.substituteSystem S r a).val) C.system) at hU
  rw [hval] at hU
  exact hU

/--
---
conclusion: Lax369799.ContextRelabelling.evaluation_congruence
---
Relabel the context and use associativity to replace each inserted system
by its value. Equal values give the same filled context. Unfolding
invariance of the algebra is not needed.
-/
theorem evaluation_congruence {A B : RankedSet} (E : Lax369799.Algebras.Algebra B)
    (η : RankedMap A B) {k n : ℕ} (C : SetContext A k n) (hC : C.system.Deterministic)
    (S T : System A k) (U V : System A n)
    (hU : U.val = plug C S.val) (hV : V.val = plug C T.val)
    (h : E.eval k (relabelSystem η S) = E.eval k (relabelSystem η T)) :
    E.eval n (relabelSystem η U) = E.eval n (relabelSystem η V) := by
  obtain ⟨U', hu, heu⟩ := SystemEvaluation.context_evaluation E (mapContext η C) hC (relabelSystem η S)
  obtain ⟨V', hv, hev⟩ := SystemEvaluation.context_evaluation E (mapContext η C) hC (relabelSystem η T)
  have eu : relabelSystem η U = U' := by
    apply Subtype.ext
    change relabel η U.val = U'.val
    rw [hU, relabel_plug, hu]
    rfl
  have ev : relabelSystem η V = V' := by
    apply Subtype.ext
    change relabel η V.val = V'.val
    rw [hV, relabel_plug, hv]
    rfl
  rw [eu, ev, heu, hev, h]

end Lax369799Proofs.ContextRelabelling
