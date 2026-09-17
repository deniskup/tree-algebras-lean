import Lax369799.SystemEvaluation

/-!
---
title: Relabelling and deterministic context substitution
type: theorem
---
Relabelling ordinary letters preserves the unique hole. It commutes with
substitution, and plugging a deterministic system into a deterministic
context gives a deterministic system.
-/
namespace Lax369799.ContextRelabelling
open RankedSystems Flattening

def mapAlphabet {A B : RankedSet} (η : RankedMap A B) (k : ℕ) :
    RankedMap (WithHole A k) (WithHole B k) := fun r => Sum.map (η r) id

def mapContext {A B : RankedSet} (η : RankedMap A B) {k n : ℕ}
    (C : SetContext A k n) : SetContext B k n where
  system := relabel (mapAlphabet η k) C.system
  one_hole := by
    have hi (v : C.system.Vertex) :
        IsHole ((relabel (mapAlphabet η k) C.system).graph.label v) ↔
          IsHole (C.system.graph.label v) := by
      change (∃ h, Sum.map (η _) id (C.system.graph.label v).2 = Sum.inr h) ↔
        ∃ h, (C.system.graph.label v).2 = Sum.inr h
      cases (C.system.graph.label v).2 <;> simp
    obtain ⟨v, hv, hu⟩ := C.one_hole
    exact ⟨v, (hi v).mpr hv, fun w hw => hu w ((hi w).mp hw)⟩

axiom relabel_plug {A B : RankedSet} (η : RankedMap A B) {k n : ℕ}
    (C : SetContext A k n) (S : SetSystem A k) :
    relabel η (plug C S) = plug (mapContext η C) (relabel η S)

axiom plug_system {A : RankedSet} {k n : ℕ}
    (C : SetContext A k n) (hC : C.system.Deterministic) (S : System A k) :
    ∃ U : System A n, U.val = plug C S.val

end Lax369799.ContextRelabelling
