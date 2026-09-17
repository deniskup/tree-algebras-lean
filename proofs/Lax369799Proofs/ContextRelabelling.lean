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

end Lax369799Proofs.ContextRelabelling
