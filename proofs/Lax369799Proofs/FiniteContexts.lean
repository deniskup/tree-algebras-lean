import Lax369799.FiniteContexts
import Lax369799Proofs.UntrimmedFlattening

namespace Lax369799Proofs.FiniteContexts
open Lax369799.RankedSystems (RankedSet RankedMap Symbol Presentation)
open Lax369799.FinitePresentations
open Lax369799.FiniteContexts
open Lax369799.Flattening (WithHole IsHole)
open Lax369799Proofs.UntrimmedFlattening

private theorem insertion_hole {A : RankedSet} {k n : ℕ}
    (C : Context A k n) (a : Symbol (WithHole A n)) :
    (∃ u, IsHole ((insertion C a.1 a.2).graph.label u)) ↔ IsHole a := by
  obtain ⟨r, a⟩ := a
  cases a with
  | inl a =>
    constructor
    · rintro ⟨u, h, he⟩; cases he
    · rintro ⟨h, he⟩; cases he
  | inr h =>
    obtain ⟨h⟩ := h
    subst r
    exact ⟨fun _ => ⟨⟨rfl⟩, rfl⟩, fun _ => C.one_hole.exists⟩

private theorem insertion_unique {A : RankedSet} {k n : ℕ}
    (C : Context A k n) (a : Symbol (WithHole A n)) (h : IsHole a) :
    ∃! u, IsHole ((insertion C a.1 a.2).graph.label u) := by
  obtain ⟨r, a⟩ := a
  cases a with
  | inl a => obtain ⟨h, he⟩ := h; cases he
  | inr eq => obtain ⟨hr⟩ := eq; subst r; exact C.one_hole

private theorem composition_one_hole {A : RankedSet} {k n m : ℕ}
    (D : Context A n m) (C : Context A k n) :
    ∃! v, IsHole ((compositionSystem D C).graph.label v) := by
  classical
  let P := relabel (insertion C) D.system
  let G := flattenPresentation P.graph
  obtain ⟨v, hv, hvu⟩ := D.one_hole
  obtain ⟨u, hu, huu⟩ := insertion_unique C (D.system.graph.label v) hv
  let z : (v : P.Vertex) × (Inner P.graph v).Vertex := ⟨v, u⟩
  have hz : ∀ w, IsHole (G.label w) → w = z := by
    rintro ⟨w, t⟩ ht
    have hw : w = v := hvu w ((insertion_hole C (D.system.graph.label w)).mp ⟨t, ht⟩)
    subst w
    exact congrArg (Sigma.mk v) (huu t ht)
  let e := Fintype.equivFin ((v : P.Vertex) × (Inner P.graph v).Vertex)
  refine ⟨e z, ?_, ?_⟩
  · change IsHole (G.label (e.symm (e z)))
    rw [e.symm_apply_apply]
    exact hu
  · intro w hw
    apply e.symm.injective
    rw [e.symm_apply_apply]
    exact hz (e.symm w) hw

private noncomputable def compose {A : RankedSet} {k n m : ℕ}
    (D : Context A n m) (C : Context A k n) : Context A k m :=
  ⟨compositionSystem D C, composition_one_hole D C⟩

/--
---
conclusion: Lax369799.FiniteContexts.composition
---
The composite retains the inner hole even when it is unreachable.
Associativity and naturality of unpruned substitution, followed by the
atomic unit isomorphisms on ordinary labels, identify its substitutions.
-/
theorem composition {A : RankedSet} {k n m : ℕ}
    (D : Context A n m) (C : Context A k n) :
    ∃ E : Context A k m, E.system = compositionSystem D C ∧
      ∀ S, Isomorphic (plug E S) (plug D (plug C S)) := by
  refine ⟨compose D C, rfl, fun S => ?_⟩
  let F : RankedMap (WithHole A n) (FiniteSystem (FiniteSystem A)) :=
    fun r a => relabel (substitution S) (insertion C r a)
  have ha := UntrimmedFlattening.flatten_associative (relabel F D.system)
  have hb := flatten_labels_iso D.system (fun r a => flatten (F r a))
    (substitution (plug C S)) (by
      intro r a
      cases a with
      | inl a => exact UntrimmedFlattening.outer_atomic (Lax369799.FinitePresentations.atomic a)
      | inr h =>
        obtain ⟨h⟩ := h
        subst r
        exact ⟨isoRefl (plug C S).graph⟩)
  obtain ⟨fa⟩ := ha
  obtain ⟨fb⟩ := hb
  change Isomorphic (flatten (relabel (substitution S)
    (flatten (relabel (insertion C) D.system)))) _
  rw [UntrimmedFlattening.flatten_natural]
  exact ⟨isoTrans fa fb⟩

private def extendLabel {A B : RankedSet} {k : ℕ}
    (f : RankedMap B (FiniteSystem A)) :
    RankedMap (WithHole B k) (FiniteSystem (WithHole A k)) :=
  fun r b => match b with
    | .inl b => relabel (fun _ a => Sum.inl a) (f r b)
    | .inr h => atomic (.inr h)

private theorem extension_holes {A B : RankedSet} {k : ℕ}
    (f : RankedMap B (FiniteSystem A)) (a : Symbol (WithHole B k)) :
    ((∃ u, IsHole ((extendLabel f a.1 a.2).graph.label u)) ↔ IsHole a) ∧
    (IsHole a → ∃! u, IsHole ((extendLabel f a.1 a.2).graph.label u)) := by
  obtain ⟨r, a⟩ := a
  cases a with
  | inl a =>
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · rintro ⟨u, h, he⟩; cases he
    · rintro ⟨h, he⟩; cases he
    · rintro ⟨h, he⟩; cases he
  | inr h =>
    refine ⟨⟨fun _ => ⟨h, rfl⟩, fun _ => ⟨(0 : Fin 1), h, rfl⟩⟩, ?_⟩
    intro _
    exact ⟨(0 : Fin 1), ⟨h, rfl⟩, fun _ _ => Subsingleton.elim (α := Fin 1) _ _⟩

private noncomputable def extendContext {A B : RankedSet}
    (f : RankedMap B (FiniteSystem A)) {k n : ℕ} (C : Context B k n) : Context A k n where
  system := flatten (relabel (extendLabel f) C.system)
  one_hole := by
    classical
    let P := relabel (extendLabel f) C.system
    let G := flattenPresentation P.graph
    obtain ⟨v, hv, hvu⟩ := C.one_hole
    obtain ⟨u, hu, huu⟩ := (extension_holes f (C.system.graph.label v)).2 hv
    let z : (v : P.Vertex) × (Inner P.graph v).Vertex := ⟨v, u⟩
    have hz : ∀ w, IsHole (G.label w) → w = z := by
      rintro ⟨w, t⟩ ht
      have hw : w = v := hvu w ((extension_holes f (C.system.graph.label w)).1.mp ⟨t, ht⟩)
      subst w
      exact congrArg (Sigma.mk v) (huu t ht)
    let e := Fintype.equivFin ((v : P.Vertex) × (Inner P.graph v).Vertex)
    refine ⟨e z, ?_, ?_⟩
    · change IsHole (G.label (e.symm (e z)))
      rw [e.symm_apply_apply]
      exact hu
    · intro w hw
      apply e.symm.injective
      rw [e.symm_apply_apply]
      exact hz (e.symm w) hw

/--
---
conclusion: Lax369799.FiniteContexts.extension
---
Expand ordinary labels into their assigned presentations while retaining
an atomic hole. Only that component has a hole-labelled vertex. The
substitution associator and the two unit laws prove the extension law.
-/
theorem extension {A B : RankedSet} (f : RankedMap B (FiniteSystem A))
    {k n : ℕ} (C : Context B k n) :
    ∃ D : Context A k n, ∀ S,
      Isomorphic (plug D S) (flatten (relabel (interpretation f S) C.system)) := by
  refine ⟨extendContext f C, fun S => ?_⟩
  let F : RankedMap (WithHole B k) (FiniteSystem (FiniteSystem A)) :=
    fun r a => relabel (substitution S) (extendLabel f r a)
  have ha := UntrimmedFlattening.flatten_associative (relabel F C.system)
  have hb := flatten_labels_iso C.system (fun r a => flatten (F r a))
    (interpretation f S) (by
      intro r a
      cases a with
      | inl a => exact UntrimmedFlattening.inner_atomic (f r a)
      | inr h =>
        obtain ⟨h⟩ := h
        subst r
        exact UntrimmedFlattening.outer_atomic S)
  obtain ⟨fa⟩ := ha
  obtain ⟨fb⟩ := hb
  change Isomorphic (flatten (relabel (substitution S)
    (flatten (relabel (extendLabel f) C.system)))) _
  rw [UntrimmedFlattening.flatten_natural]
  exact ⟨isoTrans fa fb⟩

end Lax369799Proofs.FiniteContexts
