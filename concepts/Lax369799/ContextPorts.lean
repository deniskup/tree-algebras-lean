import Lax369799.ContextRelabelling
import Lax369799.SupportPorts

/-!
---
title: Restricting and resizing the directions of a context
type: theorem
---
Select the hole's successors using a map from new directions to old
ones, change the hole rank, and restrict to reachable vertices. The
hole remains reachable because its first visit uses no outgoing hole
edge. Substitution into this context is isomorphic to renaming the
argument's outputs before insertion into the original context.
-/

namespace Lax369799.ContextPorts
open RankedSystems Flattening

/-- Change the hole's rank and retain every ordinary symbol. -/
def resizeSymbol {A : RankedSet} {m : ℕ} (k : ℕ) : Symbol (WithHole A m) → Symbol (WithHole A k)
  | ⟨r,.inl a⟩ => ⟨r,.inl a⟩
  | ⟨_,.inr _⟩ => ⟨k,.inr ⟨rfl⟩⟩

noncomputable def resizeGraph {A : RankedSet} {m k : ℕ} (C : SetContext A m 0)
    (s : Fin k → Fin m) : Presentation (WithHole A k) 0 C.system.Vertex := by
  classical
  exact {
    label := fun v => resizeSymbol k (C.system.graph.label v)
    initial := C.system.graph.initial
    root := C.system.graph.root
    edge := fun v d t => if IsHole (C.system.graph.label v) then
      ∃ i : Fin k,d = i.val ∧ C.system.graph.edge v (s i).val t
      else C.system.graph.edge v d t
    direction_valid := by
      intro v d t ht
      cases hlabel : C.system.graph.label v with
      | mk r a =>
        cases a with
        | inl a =>
          have hn : ¬IsHole (C.system.graph.label v) := by
            rw [hlabel]; rintro ⟨e,he⟩; cases he
          rw [if_neg hn] at ht
          have hd := C.system.graph.direction_valid v d t ht
          rw [hlabel] at hd
          simpa only [hlabel,resizeSymbol] using hd
        | inr e =>
          have hh : IsHole (C.system.graph.label v) := by rw [hlabel]; exact ⟨e,rfl⟩
          rw [if_pos hh] at ht
          obtain ⟨i,rfl,_⟩ := ht
          simpa only [hlabel,resizeSymbol] using i.isLt }

axiom resize_exists {A : RankedSet} {m k : ℕ} (C : SetContext A m 0)
    (hC : C.system.Deterministic) (s : Fin k → Fin m) :
    ∃ D : SetContext A k 0, D.system = trim (resizeGraph C s) ∧ D.system.Deterministic

axiom plug_resize {A : RankedSet} {m k : ℕ} (C : SetContext A m 0)
    (hC : C.system.Deterministic) (s : Fin k → Fin m) (R : System A k)
    (D : SetContext A k 0) (hD : D.system = trim (resizeGraph C s))
    (U V : System A 0) (hU : U.val = plug C (Renaming.renameSystem s R).val)
    (hV : V.val = plug D R.val) : Morphisms.Isomorphic U.val V.val

end Lax369799.ContextPorts
